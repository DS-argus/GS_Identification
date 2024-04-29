# from npsem.model import CD
from model import CD
from probability import Probability, get_new_probability
from utils import get_prev_orders

# Define exceptions that can occur.
class HedgeFound(Exception):
    '''Exception raised when a hedge is found.'''

    def __init__(self, g1, g2, message="Causal effect not identifiable. A hedge has been found:"):
        self._message = message
        super().__init__(self._message + f"\n\nC-Forest 1:\n: {g1} \n\nC-Forest 2:\n: {g2}")


class ThicketFound(Exception):
    '''Exception raised when a thicket is found.'''

    def __init__(self, message="Causal effect not identifiable. A thicket has been found:"):
        self._message = message
        super().__init__(self._message)


def myID(Y: set, X: set, G: "CD", P: "Probability" = None, order: list = None, verbose: bool = False, tab: int = 0):
    """
    OUTPUT : Expression in Latex 
    Shpitser, Pearl 2006
    [Identification of Joint Interventional Distributions in Recursive Semi-Markovian Causal Models]
    """

    Vs = G.V
    if not order: order = G.causal_order()
    if not P: P = Probability(var=Vs)

    # Line 1
    if not X:
        if verbose: print(f"[(ID) line 1]")

        P_out = P.copy()
        P_out._sumset = P._sumset | (Vs - Y)
        P_out.simplify()

        return P_out
        
    # line 2
    if Vs != G.An(Y):
        if verbose: print(f"[(ID) line 2]\tVs: {Vs}  G.An(Y): {G.An(Y)}")

        P_out = P.copy()
        P_out._sumset = P._sumset | (Vs - G.An(Y))
        P_out.simplify()

        return myID(Y, X & G.An(Y), G[G.An(Y)], P_out, order, verbose, tab=tab + 1)
    
    # line 3
    if W:=(Vs - X) - G.do(X).An(Y):
        if verbose: print(f"[(ID) line 3]\tW: {W}")

        return myID(Y, X | W, G, P, order, verbose, tab=tab + 1)

    # line 4
    if len(CCs := G[Vs - X].c_components) > 1:
        if verbose: print(f"[(ID) line 4]\tCCs: {CCs}")
        
        probabilities = set()
        for CC in CCs:
            probabilities.add(myID(CC, Vs - CC, G, P, order, verbose, tab=tab + 1))
        
        P_out = Probability(recursive=True, children=probabilities, sumset=Vs - (Y | X))
        P_out.simplify()

        return P_out

    if len(CCs) == 1:
        S = next(iter(CCs))

        # line 5
        if G.c_components == {Vs}:
            if verbose: print(f"[(ID) line 5]\tC(G): {G.c_components}    Vs: {Vs}")
            raise HedgeFound(G, G[S])
        
        # line 6
        if S in G.c_components:
            if verbose: print(f"[(ID) line 6]\tS: {S}    C(G): {G.c_components}")
            breakpoint()

            probabilities = set()
            for vertex in S:
                new_order = get_prev_orders(order, Vs)
                cond = set(new_order[:new_order.index(vertex)])
                P_i = get_new_probability(P, {vertex}, cond=cond)
                probabilities.add(P_i)

            P_out = Probability(recursive=True, children=probabilities, sumset=S - Y)
            P_out.simplify() 

            return P_out
        
        # line 7
        for S_prime in G.c_components:
            if S < S_prime:
                if verbose: print(f"[(ID) line 7]\tS: {S}    S': {S_prime}")
                
                probabilities = set()
                for vertex in S_prime:
                    new_order = get_prev_orders(order, Vs)
                    cond = set(new_order[:new_order.index(vertex)])
                    P_i = get_new_probability(P, {vertex}, cond=cond)
                    probabilities.add(P_i)

                P_out = Probability(recursive=True, children=probabilities, scope=S_prime)
                P_out.simplify()

                return myID(Y, X & S_prime, G[S_prime], P_out, order, verbose, tab=tab + 1)


def mygID(Y: set, X: set, Z:set, G: "CD", P: "Probability" = None, verbose: bool = False, tab: int = 0):
    """
    OUTPUT : Expression in Latex 
    Lee, Correa, Bareinboim 2019
    [General Identifiability with Arbitrary Surrogate Experiments]
    """
    Vs = G.V
    if not P: P = Probability(var=Vs)

    # line 2
    for z in Z:
        if X == z & Vs:
            if verbose: print(f"[(gID) line 2]\tX: {X}    Z∩V: {z & Vs}")
            
            P_out = P.copy()
            P_out._do = (z - Vs) | X
            P_out._sumset = P._sumset | (Vs - Y)
            P_out.simplify()

            return P_out

    # line 3
    if Vs != G.An(Y):
        if verbose: print(f"[(gID) line 3]\tVs: {Vs}  G.An(Y): {G.An(Y)}")
        
        P_out = P.copy()
        P_out._sumset = P._sumset | (Vs - G.An(Y))
        P_out.simplify()

        return mygID(Y, X & G.An(Y), Z, G[G.An(Y)], P_out, verbose, tab=tab + 1)
    
    # line 4
    if W := (Vs - X) - G.do(X).An(Y):
        if verbose: print(f"[(gID) line 4]\tW: {W}")

        return mygID(Y, X | W, Z, G, P, verbose, tab=tab+1)
    
    # line 6
    if len(CCs := G[Vs - X].c_components) > 1:
        if verbose: print(f"[(gID) line 6]\tG(C\X): {CCs}")

        probabilities= set()
        for CC in CCs:
            probabilities.add(mygID(CC, Vs - CC, Z, G, P, verbose, tab=tab+1))
        
        P_out = Probability(recursive=True, children=probabilities, sumset=Vs - (Y | X)) 
        P_out.simplify()

        return P_out
        
    # line 7
    for z in Z:
        if X >= z & Vs:
            if verbose: print(f"[(gID) line 7]\tX: {X}    Z∩V: {z & Vs}")

            P_out = P.copy()
            P_out._do = (z - Vs) | (X & z)
            P_out._var = Vs       # useless?
            P_out.simplify()

            result = mysubID(Y, X - z, G[Vs - (z & X)], P_out, verbose=verbose, tab=tab+1) 
            
            if result: return result

    # line 8
    if verbose: print("(gID) line 8")
    raise ThicketFound()   
        

def mysubID(Y: set, X: set, G: "CD", Q: "Probability", order: list = None, verbose: bool = False, tab: int = 0):

    Vs = G.V
    if not order: order = G.causal_order()
    S = next(iter(G[Vs - X].c_components))
    
    # line 11
    if not X:
        if verbose: print("[(subID) line 11]")
        
        Q_out = Q.copy()
        Q_out._sumset = Q._sumset | (Vs - Y)
        Q_out.simplify()

        return Q_out

    # line 12
    if Vs != G.An(Y):
        if verbose: print(f"[(subID) line 12]\tVs: {Vs}  G.An(Y): {G.An(Y)}")
        
        Q_out = Q.copy()
        Q_out._sumset = Q._sumset | (Vs - G.An(Y))
        Q_out.simplify()

        return mysubID(Y, X & G.An(Y), G[G.An(Y)], Q_out, order, verbose, tab=tab + 1)
    
    # line 13
    if (CCs:=G.c_components) == {Vs}:
        if verbose: print(f"[(subID) line 13]\tC(G): {G.c_components}    Vs: {Vs}")
        
        return None
    
    # line 14
    if S in CCs:
        if verbose: print(f"[(subID) line 14]\tS: {S}   C(G): {CCs}")
        
        probabilities = set()
        for vertex in S:
            new_order = get_prev_orders(order, Vs)
            cond = set(new_order[:new_order.index(vertex)])
            Q_i = get_new_probability(Q, {vertex}, cond=cond)
            probabilities.add(Q_i)

        Q_out = Probability(recursive=True, children=probabilities, sumset=S - Y)
        Q_out.simplify()

        return Q_out
    
    # line 15
    for S_prime in CCs:
        if S < S_prime:
            if verbose: print(f"[(subID) line 15]\tS: {S}   S': {S_prime}")

            probabilities = set()
            for vertex in S_prime:
                new_order = get_prev_orders(order, Vs)
                cond = set(new_order[:new_order.index(vertex)])
                Q_i = get_new_probability(Q, {vertex}, cond=cond)
                probabilities.add(Q_i)
            
            Q_out = Probability(recursive=True, children=probabilities, scope=S_prime)
            Q_out.simplify()
            
            return mysubID(Y, X & S_prime, G[S_prime], Q_out, order, verbose, tab=tab + 1)


if __name__ == "__main__":

    G = CD({'X', 'Z', 'Y'}, 
        [('X', 'Z'), ('Z', 'Y')],
        [('Z', 'Y', 'U')])

    P2 = mygID(Y=set(["Y"]), X=set(["X"]), Z=frozenset([frozenset()]), G=G)
    print(f"mygID")
    print(P2.printLatex())