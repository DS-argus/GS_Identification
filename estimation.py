from probability import Probability
from typing import Iterable

class Node:
    def __init__(self):
        self.__children = []
    
    def add_child(self, child: Probability):
        self.__children += [child]

class ProbNode(Node):
    def __init__(self, prob: Probability, inverse: bool):
        super().__init__()
        self.prob = prob
        self.inverse = inverse

class SumNode(Node):
    def __init__(self, sumset):
        super().__init__()
        self.sumset = sumset

class ProductNode(Node):
    def __init__(self):
        super().__init__()
        self.__inversed_children = []

    def add_child(self, child: Probability, inverse: bool):
        if inverse:
            self.__inversed_children += [child]
        else:
            return super().add_child(child)
    

def build_tree(parent: Node, prob: Probability):
    if prob._divisor:
        # 분수인 경우, ProductNode 생성하고(역수로 처리) divisor에 대해 build tree
        ProductTerm = ProductNode()
        parent.add_child(ProductTerm)
        temp = prob.copy()
        temp._fraction = False
        temp._divisor = None

        denomNode = ProbNode(prob._divisor, inverse=True)
        numerNode = ProbNode(temp)

        ProductTerm.add_child(denomNode)
        ProductTerm.add_child(numerNode)

        build_tree(denomNode, prob._divisor)
        build_tree(numerNode, temp)

    elif prob._sumset:
        sigma = SumNode(prob._sumset)
        if not prob._recursive:
            temp = prob.copy()
            temp._sumset = set()
            sigma.add_child(temp)
        else:
            for child in prob._children:
                sigma.add_child(child)
                build_tree()

    
    if prob._recursive:
        # recursive한 경우, SumNode 또는 ProductNode 처리


        else:
            node = ProductNode()
        for child in prob["children"]:
            build_tree(child, node)
        if parent:
            parent.children.append(node)
        return node
    else:
        # leaf node인 경우, TermNode 생성
        term_node = TermNode(prob["var"], prob["cond"], prob["do"])
        if parent:
            parent.children.append(term_node)
        return term_node
