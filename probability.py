import re
import copy
from itertools import permutations

# Define a probability distribution class
class Probability:
    '''
    condition은 get_new_probability로 우선 fraction 형태로 처리되고 가능한 경우 simplify에서 _var|_cond 로 변경됨
    '''

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
    

    def simplify(self):

        # for loop 돌면서 children 만드는 경우 children이 1개면 불필요하게 nested 됨
        # 밖으로 꺼내주고 이미 get_new_probability에서 simplify해서 추가적인 정리 필요 없음        
        if self._recursive and len(self._children)==1:
            child = next(iter(self._children))
            self.__dict__ = child.__dict__      # child의 정보를 self에 복사
            return
        
        # get_new_probability에서 simplify 를 해서 안해도 될 것 같음
        if self._divisor:
            self._divisor.simplify()
        
        # 한번이라도 simplify가 되었다면 다시 탐색
        # self._sumset, self._recursive, self._fraction 의 유무에 따라 simplify 방법 달라짐
        flag = True 
        while flag:
            flag = False
            
            # sumset도 없고, children도 없고, fraction도 없다면
            if not self._sumset and not self._recursive and not self._fraction:
                return 

            # sumset이 있는데, children이 없고, fraction도 없다면
            # sum_c P(a, c) = P(a)
            elif self._sumset and not self._recursive and not self._fraction:
                sum_variables = self._sumset & self._var
                self._sumset = self._sumset - sum_variables
                self._var = self._var - sum_variables
                flag = True

            # children있으면서, fraction 있는 경우
            elif not self._recursive and self._fraction:
                
                # P(x, y) / P() = P(x, y)
                if not self._divisor._var:
                    self._divisor = None
                    self._fraction = False
                    flag = True


                # 만약 분모의 condition이 없고 divisor의 V가 분자 V의 부분집합이면 분모 제거
                # P(x, y) / P(y) = P(x|y)
                elif not self._divisor._cond and self._divisor._var<=self._var:
                    self._var = self._var - self._divisor._var
                    self._cond = self._cond | self._divisor._var
                    self._divisor = None
                    self._fraction = False
                    flag = True
            
            # children이 있는 경우 child끼리 합칠 수 있는지 확인
            elif self._recursive:
                
                for prob1, prob2 in permutations(self._children, 2):
                    
                    # 모두 children이 없다면
                    if not prob1._recursive and not prob2._recursive:
                        
                        # P(Y|X,Z)P(X|Z) = P(Y,X|Z), P(Y|X)P(X) = P(Y,X)
                        if prob1._cond == prob2._var | prob2._cond:
                            removable = prob2
                            prob1._var = prob1._var | prob2._var
                            prob1._cond = prob1._cond - prob2._var
                            self._children -= {removable}   # 합쳐져서 없어진 것 제거 (prob2)
                            
                            # 만약 children이 하나가 남으면 recursive False로 하고 올려줌
                            if len(self._children) == 1:
                                prob = next(iter(self._children))
                                self.__dict__ = prob.__dict__

                            flag = True      # 또 다른 simplify를 위해서 while문 돌아야 함

                    if flag:  # 일단 하나 simplify 했으면 넘어감
                        break
                
            # sum_c P(a, c|x, y, z) P(x | a, y)  = P(a | x, y, z) P(x | a, y)
            # 대신 모든 children이 recursive가 없어야 함. 있는 경우 그 안에 self.sumset에 해당하는 변수가 있을 수 있어 함부로 지울 수 없음
            if self._sumset and self._recursive and not any(child._recursive for child in self._children):
                vars, conds = set(), set()
                for child in self._children:
                    vars |= child._var
                    conds |= child._cond
                
                for child in self._children:
                    if removable := (child._var - conds) & self._sumset:
                        child._var  -= removable
                        self._sumset -= removable
                        if not child._var:
                            self._children -= {child}
                        flag = True
                        break


    def __lt__(self, other):
        # 1. _cond가 있는 객체는 없는 객체보다 후순위
        if self._sumset and not other._sumset:
            return False
        elif not self._sumset and other._sumset:
            return True
        
        if self._cond and not other._cond:
            return False
        elif not self._cond and other._cond:
            return True
        
        # 2. _var의 개수가 클수록 후순위
        if len(self._var) < len(other._var):
            return True
        elif len(self._var) > len(other._var):
            return False
        else:
            # 3. _var 개수가 같다면 _var의 원소 중 가장 작은 것을 포함한 객체를 더 선순위
            # 4. _var을 정렬할 때는 먼저 알파벳 순서로 정렬하고 알파벳이 같으면 숫자 순으로 정렬. 숫자가 없는 것은 0으로 간주
            sorted_self_var = sorted(self._var, key=lambda x: (x.strip('0123456789'), int(''.join(filter(str.isdigit, x)) or '0')))
            sorted_other_var = sorted(other._var, key=lambda x: (x.strip('0123456789'), int(''.join(filter(str.isdigit, x)) or '0')))
            
            return sorted_self_var < sorted_other_var


    @staticmethod # 출력할 때 W1을 w_1로 출력하기 위한 함수
    def underscore(input_set: frozenset):
        # Regular expression to find digits
        input_set = set(input_set)

        pattern = r'(\d+)'
    
        # Add an underscore before each number in each string of the set
        modified_set = {re.sub(pattern, r'_\1', item) for item in input_set}
        
        return modified_set


    def printLatex(self, tab=0):
        '''Function that returns a string in LaTeX syntax of the probability distribution.'''
        
        out = ""
        if self._fraction:
            out += '\\left(\\frac{'
        
        if self._sumset:
            if tab == 0:
                out += '\sum_{' + ', '.join(sorted(self.underscore(self._sumset))).lower() + '}'
            else:
                out += '\\left(\sum_{' + ', '.join(sorted(self.underscore(self._sumset))).lower() + '}'
        
        if not self._recursive:
            if self._var:
                if self._do:
                    out += 'P_{'+ ', '.join(sorted(self.underscore(self._do))).lower() +'}(' + ', '.join(sorted(self.underscore(self._var))).lower()
                else:
                    out += 'P(' + ', '.join(sorted(self.underscore(self._var))).lower()
                if self._cond:
                    out += '|' + ', '.join(sorted(self.underscore(self._cond))).lower()
                out += ')'
            else:   # useless?
                out += '1'
        else:
            for prob in sorted(self._children):
                out += prob.printLatex(tab=tab + 1)
        if self._sumset and tab:
            out += '\\right)'
        
        if self._fraction:
            out += '}{'
            out += self._divisor.printLatex()
            out += '}\\right)'
        
        return out


def get_new_probability(P, var, cond={}):
    '''
    ID 알고리즘 line 6, 7에서 cond에는 있지만 S'에 속하지 않는 변수는 Freevariables에서 제거해야 함
    '''

    P_out = P.copy()

    if len(cond) == 0:
        P_out._sumset = P_out._sumset | (P.getFreeVariables() - var)
        P_out.simplify()
    else:
        P_denom = P.copy()
        P_out._sumset = P_out._sumset | (P.getFreeVariables() - (cond | var))
        P_out.simplify()    # 분자 simplify
        
        P_out._fraction = True
        P_denom._sumset = P_denom._sumset | (P.getFreeVariables()- cond)
        P_denom.simplify()  # 분모 simplify
        P_out._divisor = P_denom

    P_out.simplify()

    return P_out

if __name__ == "__main__":
    pass