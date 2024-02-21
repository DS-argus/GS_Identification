import functools
import itertools
import networkx as nx
import matplotlib.pyplot as plt

from typing import FrozenSet, Tuple
from collections import defaultdict
from typing import Iterable, Optional, Set, Sequence, AbstractSet
from utils import fzset_union, sortup, sortup2, dict_only, dict_except, pairs2dict, wrap


class CausalDiagram:
    def __init__(self,
                 vs: Optional[Iterable[str]],
                 directed_edges: Optional[Iterable[Tuple[str, str]]] = frozenset(),
                 bidirected_edges: Optional[Iterable[Tuple[str, str, str]]] = frozenset(),
                 copy: 'CausalDiagram' = None,
                 with_do: Optional[Set[str]] = None,
                 with_induced: Optional[Set[str]] = None):
        with_do = wrap(with_do)
        with_induced = wrap(with_induced)

        if copy is not None:
            if with_do is not None:
                self.V = copy.V
                self.U = wrap(u for u in copy.U if with_do.isdisjoint(copy.confounded_dict[u]))
                self.confounded_dict = {u: val for u, val in copy.confounded_dict.items() if u in self.U}

                # copy cautiously
                dopa = copy.pa(with_do)
                doAn = copy.An(with_do)
                doDe = copy.De(with_do)

                self._pa = defaultdict(frozenset, {k: frozenset() if k in with_do else v for k, v in copy._pa.items()})
                self._ch = defaultdict(frozenset, {k: (v - with_do) if k in dopa else v for k, v in copy._ch.items()})
                self._an = dict_except(copy._an, doDe)
                self._de = dict_except(copy._de, doAn)

            elif with_induced is not None: 
                assert with_induced <= copy.V
                removed = copy.V - with_induced
                self.V = with_induced
                self.confounded_dict = {u: val for u, val in copy.confounded_dict.items() if val <= self.V}
                self.U = wrap(self.confounded_dict)

                children_are_removed = copy.pa(removed) & self.V
                parents_are_removed = copy.ch(removed) & self.V
                ancestors_are_removed = copy.de(removed) & self.V
                descendants_are_removed = copy.an(removed) & self.V

                self._pa = defaultdict(frozenset, {x: (copy._pa[x] - removed) if x in parents_are_removed else copy._pa[x] for x in self.V})
                self._ch = defaultdict(frozenset, {x: (copy._ch[x] - removed) if x in children_are_removed else copy._ch[x] for x in self.V})
                self._an = dict_only(copy._an, self.V - ancestors_are_removed)
                self._de = dict_only(copy._de, self.V - descendants_are_removed)
            else:
                self.V = copy.V
                self.U = copy.U
                self.confounded_dict = copy.confounded_dict
                self._ch = copy._ch
                self._pa = copy._pa
                self._an = copy._an
                self._de = copy._de
        else:
            directed_edges = list(directed_edges)
            bidirected_edges = list(bidirected_edges)
            self.V = frozenset(vs) | fzset_union(directed_edges) | fzset_union((x, y) for x, y, _ in bidirected_edges)
            self.U = frozenset(u for _, _, u in bidirected_edges)
            self.confounded_dict = {u: frozenset({x, y}) for x, y, u in
                                    bidirected_edges}

            self._ch = pairs2dict(directed_edges)
            self._pa = pairs2dict(directed_edges, backward=True)
            self._an = dict()  # cache
            self._de = dict()  # cache
            assert self._ch.keys() <= self.V and self._pa.keys() <= self.V
        
        if bidirected_edges == None:
            self.bidirected_edges = []
        else:
            self.bidirected_edges = list(bidirected_edges)
        self.edges = tuple((x, y) for x, ys in self._ch.items() for y in ys)

        self.causal_order = functools.lru_cache()(self.causal_order)
        self._do_ = functools.lru_cache()(self._do_)
        self.__cc = None
        self.__cc_dict = None
        self.__h = None
        self.__characteristic = None
        self.__confoundeds = None
        self.u_pas = defaultdict(set)
        for u, xy in self.confounded_dict.items():
            for v in xy:
                self.u_pas[v].add(u)

        self.u_pas = defaultdict(set, {v: frozenset(us) for v, us in self.u_pas.items()})


    def UCs(self, v):
        return self.u_pas[v]


    def __contains__(self, item):
        if isinstance(item, str):   
            return item in self.V or item in self.U
        if len(item) == 2:          
            if isinstance(item, AbstractSet):
                x, y = item
                return self.is_confounded(x, y)
            else:                   
                return tuple(item) in self.edges
        if len(item) == 3:
            x, y, u = item          
            return self.is_confounded(x, y) and u in self.confounded_dict and self.confounded_dict[u] == frozenset({x, y})
        return False


    def __lt__(self, other):
        if not isinstance(other, CausalDiagram):
            return False
        return self <= other and self != other
    

    def __le__(self, other):
        if not isinstance(other, CausalDiagram):
            return False
        return self.V <= other.V and set(self.edges) <= set(other.edges) and set(self.confounded_dict.values()) <= set(other.confounded_dict.values())


    def __ge__(self, other):
        if not isinstance(other, CausalDiagram):
            return False
        return self.V >= other.V and set(self.edges) >= set(other.edges) and set(self.confounded_dict.values()) >= set(other.confounded_dict.values())


    def __gt__(self, other):
        if not isinstance(other, CausalDiagram):
            return False
        return self >= other and self != other


    def Pa(self, v_or_vs) -> FrozenSet:
        return self.pa(v_or_vs) | wrap(v_or_vs, frozenset)


    def pa(self, v_or_vs) -> FrozenSet:
        if isinstance(v_or_vs, str):
            return self._pa[v_or_vs]
        else:
            return fzset_union(self._pa[v] for v in v_or_vs)


    def ch(self, v_or_vs) -> FrozenSet:
        if isinstance(v_or_vs, str):
            return self._ch[v_or_vs]
        else:
            return fzset_union(self._ch[v] for v in v_or_vs)


    def Ch(self, v_or_vs) -> FrozenSet:
        return self.ch(v_or_vs) | wrap(v_or_vs, frozenset)


    def An(self, v_or_vs) -> FrozenSet:
        if isinstance(v_or_vs, str):
            return self.__an(v_or_vs) | {v_or_vs}
        return self.an(v_or_vs) | wrap(v_or_vs, frozenset)


    def an(self, v_or_vs) -> FrozenSet:
        if isinstance(v_or_vs, str):
            return self.__an(v_or_vs)
        return fzset_union(self.__an(v) for v in wrap(v_or_vs))


    def De(self, v_or_vs) -> FrozenSet:
        if isinstance(v_or_vs, str):
            return self.__de(v_or_vs) | {v_or_vs}
        return self.de(v_or_vs) | wrap(v_or_vs, frozenset)


    def de(self, v_or_vs) -> FrozenSet:
        if isinstance(v_or_vs, str):
            return self.__de(v_or_vs)
        return fzset_union(self.__de(v) for v in wrap(v_or_vs))


    def __an(self, v) -> FrozenSet:
        if v in self._an:
            return self._an[v]
        self._an[v] = fzset_union(self.__an(parent) for parent in self._pa[v]) | self._pa[v]
        return self._an[v]


    def __de(self, v) -> FrozenSet:
        if v in self._de:   
            return self._de[v]
        self._de[v] = fzset_union(self.__de(child) for child in self._ch[v]) | self._ch[v]
        return self._de[v]


    def do(self, v_or_vs) -> 'CausalDiagram':
        return self._do_(wrap(v_or_vs))


    def _do_(self, v_or_vs) -> 'CausalDiagram':
        return CausalDiagram(None, None, None, self, wrap(v_or_vs))


    def has_edge(self, x, y) -> bool:
        return y in self._ch[x]


    def is_confounded(self, x, y) -> bool:
        return {x, y} in self.confounded_dict.values()


    def u_of(self, x, y):
        key = {x, y}
        for u, ab in self.confounded_dict.items():
            if ab == key:
                return u
        return None


    def confounded_with(self, u):
        return self.confounded_dict[u]


    def confounded_withs(self, v):
        return {next(iter(xy - {v})) for xy in self.confounded_dict.values() if v in xy}


    def __getitem__(self, item) -> 'CausalDiagram':
        return self.induced(item)


    def induced(self, v_or_vs) -> 'CausalDiagram':
        if set(v_or_vs) == self.V:
            return self
        return CausalDiagram(None, None, None, copy=self, with_induced=v_or_vs)


    @property
    def characteristic(self):
        if self.__characteristic is None:
            self.__characteristic = (len(self.V),
                                     len(self.edges),
                                     len(self.confounded_dict),
                                     sortup([(len(self.ch(v)), len(self.pa(v)), len(self.confounded_withs(v))) for v in self.V]))
        return self.__characteristic


    def edges_removed(self, edges_to_remove: Iterable[Sequence[str]]) -> 'CausalDiagram':
        edges_to_remove = [tuple(edge) for edge in edges_to_remove]

        dir_edges = {edge for edge in edges_to_remove if len(edge) == 2}
        bidir_edges = {edge for edge in edges_to_remove if len(edge) == 3}
        bidir_edges = frozenset((*sorted([x, y]), u) for x, y, u in bidir_edges)
        return CausalDiagram(self.V, set(self.edges) - dir_edges, self.confounded_to_3tuples() - bidir_edges)


    def __sub__(self, v_or_vs_or_edges) -> 'CausalDiagram':
        if not v_or_vs_or_edges:
            return self
        if isinstance(v_or_vs_or_edges, str):
            return self[self.V - wrap(v_or_vs_or_edges)]
        v_or_vs_or_edges = list(v_or_vs_or_edges)
        if isinstance(v_or_vs_or_edges[0], str):
            return self[self.V - wrap(v_or_vs_or_edges)]
        return self.edges_removed(v_or_vs_or_edges)


    def causal_order(self, backward=False) -> Tuple:
        gg = nx.DiGraph(self.edges)
        gg.add_nodes_from(self.V)
        top_to_bottom = list(nx.topological_sort(gg))
        if backward:
            return tuple(reversed(top_to_bottom))
        else:
            return tuple(top_to_bottom)


    def __add__(self, edges):
        if isinstance(edges, CausalDiagram):
            return merge_two_cds(self, edges)

        directed_edges = {edge for edge in edges if len(edge) == 2}
        bidirected_edges = {edge for edge in edges if len(edge) == 3}
        return CausalDiagram(self.V, set(self.edges) | directed_edges, self.confounded_to_3tuples() | bidirected_edges)


    def __ensure_confoundeds_cached(self):
        if self.__confoundeds is None:
            self.__confoundeds = dict()
            for u, (x, y) in self.confounded_dict.items():
                if x not in self.__confoundeds:
                    self.__confoundeds[x] = set()
                if y not in self.__confoundeds:
                    self.__confoundeds[y] = set()
                self.__confoundeds[x].add(y)
                self.__confoundeds[y].add(x)
            self.__confoundeds = {x: frozenset(ys) for x, ys in self.__confoundeds.items()}
            for v in self.V:
                if v not in self.__confoundeds:
                    self.__confoundeds[v] = frozenset()


    def __ensure_cc_cached(self):
        if self.__cc is None:
            self.__ensure_confoundeds_cached()
            ccs = []
            remain = set(self.V)
            found = set()
            while remain:   
                v = next(iter(remain))
                a_cc = set()
                to_expand = [v]
                while to_expand:    # bidirected로 연결된 노드 모두 방문
                    v = to_expand.pop()
                    a_cc.add(v)
                    to_expand += list(self.__confoundeds[v] - a_cc)
                ccs.append(a_cc)    # CC list에 방금 구한 CC 추가
                found |= a_cc
                remain -= found
            self.__cc2 = frozenset(frozenset(a_cc) for a_cc in ccs)
            self.__cc_dict2 = {v: a_cc for a_cc in self.__cc2 for v in a_cc}

            self.__cc = self.__cc2
            self.__cc_dict = self.__cc_dict2


    @property
    def c_components(self) -> FrozenSet:
        self.__ensure_cc_cached()
        return self.__cc


    def c_component(self, v_or_vs) -> FrozenSet:
        assert isinstance(v_or_vs, str)
        self.__ensure_cc_cached()
        return fzset_union(self.__cc_dict[v] for v in wrap(v_or_vs))


    def confounded_to_3tuples(self) -> FrozenSet[Tuple[str, str, str]]:
        return frozenset((*sorted([x, y]), u) for u, (x, y) in self.confounded_dict.items())


    def __eq__(self, other):
        if not isinstance(other, CausalDiagram):
            return False
        if self.V != other.V:
            return False
        if set(self.edges) != set(other.edges):
            return False
        if set(self.confounded_dict.values()) != set(other.confounded_dict.values()):  # does not care about U's name
            return False
        return True


    def __hash__(self):
        if self.__h is None:
            self.__h = hash(sortup(self.V)) ^ hash(sortup(self.edges)) ^ hash(sortup2(self.confounded_dict.values()))
        return self.__h


    def __repr__(self):
        return cd2qcd(self)


    def __str__(self):
        nxG = nx.DiGraph(sortup(self.edges))
        paths = []
        while nxG.edges:
            path = nx.dag_longest_path(nxG)
            paths.append(path)
            for x, y in zip(path, path[1:]):
                nxG.remove_edge(x, y)
        nxG = nx.Graph([(x, y) for x, y in self.confounded_dict.values()])
        bipaths = []
        while nxG.edges:
            temppaths = []
            for x, y in itertools.combinations(sortup(nxG.nodes), 2):
                for spath in nx.all_simple_paths(nxG, x, y):
                    temppaths.append(spath)
            selected = sorted(temppaths, key=lambda _spath: len(_spath), reverse=True)[0]
            bipaths.append(selected)
            for x, y in zip(selected, selected[1:]):
                nxG.remove_edge(x, y)

        modified = True
        while modified:
            modified = False
            for i, path1 in enumerate(bipaths):
                for j, path2 in enumerate(bipaths[i + 1:], i + 1):
                    if path1[-1] == path2[0]:
                        newpath = path1 + path2[1:]
                        bipaths.pop(j)
                        bipaths[i] = newpath
                        break
                    elif path1[0] == path2[-1]:
                        newpath = path2 + path1[1:]
                        bipaths.pop(j)
                        bipaths[i] = newpath
                        break
                    elif path1[0] == path2[0]:
                        newpath = list(reversed(path2)) + path1[1:]
                        bipaths.pop(j)
                        bipaths[i] = newpath
                        break
                    elif path1[-1] == path2[-1]:
                        newpath = path2 + list(reversed(path1))[1:]
                        bipaths.pop(j)
                        bipaths[i] = newpath
                        break
                modified = path1 != bipaths[i]
                if modified:
                    break

        # a -> b -> c
        # e -> d -> c
        # == a->b->c<-d<-e
        paths_string = [' ⟶ '.join(path) for path in paths]
        bipaths_string = [' ⟷ '.join(path) for path in bipaths]
        alone = self.V - {x for path in paths for x in path} - {x for path in bipaths for x in path}
        if alone:
            return f'[{",".join([str(x) for x in alone])} / ' + (', '.join(paths_string) + ' / ' + ', '.join(bipaths_string)) + ']'
        else:
            return f'[' + (', '.join(paths_string) + ' / ' + ', '.join(bipaths_string)) + ']'
    
    def draw_graph(self):

        # Create a directed graph
        G = nx.DiGraph()
        
        # Add nodes
        G.add_nodes_from(self.V)
        
        # Add directed edges
        G.add_edges_from(self.edges)
        
        # Create a separate graph for bidirected edges to handle them differently in drawing
        G_bi = nx.MultiDiGraph()
        G_bi.add_nodes_from(self.V)
        G_bi.add_edges_from([(u, v) for u, v, _ in self.bidirected_edges])
        G_bi.add_edges_from([(v, u) for u, v, _ in self.bidirected_edges])  # Add reverse direction for bidirected
        
        # Draw the directed graph
        pos = nx.spring_layout(G)  # positions for all nodes
        nx.draw(G, pos, with_labels=True, node_color='lightblue', edge_color='gray', connectionstyle='arc3,rad=0.1')
        
        # Draw bidirected edges with a different style
        nx.draw_networkx_edges(G_bi, pos, edge_color='red', connectionstyle='arc')

        plt.show()


CD = CausalDiagram


if __name__ == "__main__":
    G = CausalDiagram({'X', 'Z', 'Y'}, 
                    [('X', 'Z'), ('Z', 'Y')],
                    [])
    
    print(G)
    print(G.c_components())