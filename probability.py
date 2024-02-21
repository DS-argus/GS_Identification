import copy
import re

# Define a probability distribution class
class Probability:
    '''Probability distribution class. If recursive is set to True, var and cond are ignored
    and it becomes a product of probabilities in children. If fraction is set to True, the
    divisor is enabled.'''

    def __init__(self, var=set(), cond=set(), do=set(), recursive=False, children=set(), sumset=set(), fraction=False,
                 divisor=None, scope: set = set()):
        self._var = var
        self._cond = cond
        self._do = do
        self._recursive = recursive
        self._children = children
        self._sumset = sumset
        self._fraction = fraction
        self._divisor = divisor

        # 기본적으로 scope를 var과 cond로 설정        
        if not scope:
            scope = self._var | self._cond
        self._scope = scope
        
    def copy(self):
        new_P = copy.deepcopy(self)
        return new_P

    # GetAttributes
    @property
    def attributes(self):
        '''Function that shows all attributes of the probability distribution.'''
        out = {}
        out["var"] = self._var
        out["cond"] = self._cond
        out["do"] = self._do
        out["recursive"] = self._recursive
        
        if self._recursive:
            out["children"] = [child.attributes for child in self._children]
        else:
            out["children"] = self._children
        
        out["sumset"] = self._sumset
        out["fraction"] = self._fraction
        
        if self._fraction:
            out["divisor"] = self._divisor.attributes
        else:
            out["divisor"] = self._divisor

        out["scope"] = self._scope

        return out


    def getFreeVariables(self) -> set:
        '''Function that returns the free variables of the distribution.'''
        # Probability가 정의된 random variables return : (vars - sumset) & scope

        free = set()
        
        if not self._recursive:
            free = free.union(self._var)
        else:
            for prob in self._children:
                free = free.union(prob.getFreeVariables())
        
        # summation할 변수는 제외. 
        free = free - self._sumset
        
        # 분모에 있는 변수들도 추가
        if self._fraction:
            free = free.union(self._divisor.getFreeVariables()) 

        # P가 정의된 변수들만 해당(cond에 있는 변수가 상수인 경우 제외)
        free = free & self._scope

        return free
    

    def simplify(self, complete=True, verbose=False):
        '''Function that simplifies some expressions.'''
        self.decouple()         # 일단 최대한 children으로 올리기
        changes = True
        while (changes):
            changes = False
            # 하나의 P에서 sumset과 V의 simplify
            if not self._recursive:
                # \sum_{x}P(x, y) = P(y) 로 
                sum_variables = self._sumset & self._var
                self._sumset = self._sumset - sum_variables
                self._var = self._var - sum_variables

                # 분모가 있는 경우(cond가 있어서)
                if self._fraction:
                    # 분모도 쪼개지는게 아니라면 위에서 한것처럼 sumset의 변수 v에서 제거
                    if not self._divisor._recursive:
                        sum_variables = self._divisor._sumset & self._divisor._var
                        self._divisor._sumset = self._divisor._sumset - sum_variables
                        self._divisor._var = self._divisor._var - sum_variables
                        # 만약 분모 V가 없다면 분모를 없애버리면 됨
                        if len(self._divisor._var) == 0:
                            self._divisor = None
                            self._fraction = False

                        # 만약 분모의 condition이 없고 divisor의 V가 분자 V의 부분집합이면 분모 없앨 있음 
                        # P(x, y) / P(y) = P(x|y)
                        elif len(self._divisor._cond) == 0 and self._divisor._var.issubset(self._var):
                            self._var = self._var - self._divisor._var
                            self._cond = self._cond | self._divisor._var
                            self._divisor = None
                            self._fraction = False

            # 다른 P간의 simplify
            elif complete:
                simplified = None
                for prob1 in self._children:
                    for prob2 in self._children:
                        #일단 서로 다른 prob이고 모두 하나의 term이라면 
                        if not prob1._recursive and not prob2._recursive and not prob1 == prob2:
                            # P(Y|X,Z)P(X|Z) = P(Y,X|Z), P(Y|X)P(X) = P(Y,X)
                            if prob1._cond == prob2._var | prob2._cond:
                                simplified = prob2
                                if verbose: print("Additional simplification")
                                prob1._var = prob1._var | prob2._var
                                prob1._cond = prob1._cond - prob2._var
                                changes = True      # 또 다른 simplify를 위해서 while문 돌아야 함
                        if simplified is not None:  # 일단 하나 simplify 했으면 넘어감
                            break
                    if simplified is not None:      # 일단 하나 simplify 했으면 넘어감
                        break
                
                if simplified is not None:
                    self._children.remove(simplified)   # 합쳐져서 없어진 것 제거 (prob2)
                    # 만약 children이 하나가 남으면 그냥 그걸 올리면 됨
                    if len(self._children) == 1:
                        (prob,) = self._children
                        self._sumset = prob._sumset | self._sumset
                        self._var = prob._var
                        self._cond = prob._cond
                        self._recursive = False
                        self._children = set()


    def __lt__(self, other):
        '''Function that enables alphabetical sorting of variables.'''
        if len(other._var) == 0:
            return True
        if len(self._var) == 0:
            return False
        return sorted(self._var)[0].__lt__(sorted(other._var)[0])


    @staticmethod # 출력할 때 W1을 w_1로 출력하기 위한 함수
    def underscore(input_set: frozenset):
        # Regular expression to find digits
        input_set = set(input_set)

        pattern = r'(\d+)'
    
        # Add an underscore before each number in each string of the set
        modified_set = {re.sub(pattern, r'_\1', item) for item in input_set}
        
        return modified_set

    def printLatex(self, tab=0, simplify=True, complete_simplification=True, verbose=False):
        '''Function that returns a string in LaTeX syntax of the probability distribution.'''
        if simplify:
            self.simplify(complete=complete_simplification, verbose=verbose)
            if self._recursive:
                for prob in self._children:
                    prob.simplify(complete=complete_simplification, verbose=verbose)
        out = ""
        if self._fraction:
            out += '\\left(\\frac{'
        if len(self._sumset) != 0:
            if tab == 0:
                out += '\sum_{' + ', '.join(sorted(self.underscore(self._sumset))).lower() + '}'
            else:
                out += '\\left(\sum_{' + ', '.join(sorted(self.underscore(self._sumset))).lower() + '}'
        if not self._recursive:
            if len(self._var) != 0:
                if (self._do) != 0:
                    out += 'P_{'+ ', '.join(sorted(self.underscore(self._do))).lower() +'}(' + ', '.join(sorted(self.underscore(self._var))).lower()
                else:
                    out += 'P(' + ', '.join(sorted(self.underscore(self._var))).lower()
                if len(self._cond) != 0:
                    out += '|' + ', '.join(sorted(self.underscore(self._cond))).lower()
                out += ')'
            else:
                out += '1'
        else:
            for prob in sorted(self._children):
                out += prob.printLatex(tab=tab + 1, simplify=simplify, complete_simplification=complete_simplification,
                                       verbose=verbose)
        if len(self._sumset) != 0 and tab != 0:
            out += '\\right)'
        if self._fraction:
            out += '}{'
            out += self._divisor.printLatex(simplify=simplify, complete_simplification=complete_simplification,
                                            verbose=verbose)
            out += '}\\right)'
        return out

    # children의 children을 최대한 내 chidren으로 올리는 것...?
    def decouple(self):
        '''Recursive function that decouples products of probabilities when possible to ease simplification.'''
        new_children = set()
        decouple = False
        # recursive인 경우에만, 
        if self._recursive:
            for p in self._children:
                # 만약 children도 recursive하고 sumset은 없으면 children의 children도 내 children으로 볼 수 있음
                if p._recursive and len(p._sumset) == 0:
                    decouple = True
                    subdec = p.decouple()
                    new_children = new_children | subdec._children
                # 만약 children이 recursive하지 않거나 혹은 sumset이 있으면
                else:   
                    new_children = new_children.union({p})
            if decouple:
                self._children = new_children
        return self


def get_new_probability(P, var, cond={}):
    '''
    Function that returns a new probability object P_out with variabes var conditioned on cond from
    the given probability P.

    ID 알고리즘 line 6, 7에서 cond에는 있지만 S'에 속하지 않는 변수는 Freevariables에서 제거해야 함

    '''
    ## 그래프까지 받아서 dsep확인해서 추리는 동작을 넣어볼까? 여기에 넣을지 아니면 probability class에 넣을지 고민해봐야 함

    P_out = P.copy()
    if len(cond) == 0:
        if P_out._recursive:
            P_out._sumset = P_out._sumset | (P.getFreeVariables() - var)
        else:
            P_out._var = var
    else:
        # 여기에서 식이 아주 지랄맞아지기 때문에 먼저 분자 정리해야 함
        P_denom = P.copy()
        P_out._sumset = P_out._sumset | (P.getFreeVariables() - (cond | var))
        P_out._fraction = True
        P_denom._sumset = P_denom._sumset | (P.getFreeVariables()- cond)
        P_out._divisor = P_denom
        P_out.simplify(complete=False)  # complete true로 하면 분모랑 형태 달라져서 헷갈려서 그런가?

    return P_out

if __name__ == "__main__":
    pass