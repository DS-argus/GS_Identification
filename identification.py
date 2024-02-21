from npsem.model import CD
from probability import Probability, get_new_probability

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


def get_prev_orders(order: list, left: set) -> list:
    """
    To preserve topological order in recursive calls.
    """
    return [element for element in order if element in left]


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
        if P_out._recursive:
            P_out._sumset = P._sumset | (Vs - Y)
        else:
            P_out._var = Y
        
        return P_out
        
    # line 2
    if Vs != G.An(Y):
        if verbose: print(f"[(ID) line 2]\tVs: {Vs}  G.An(Y): {G.An(Y)}")

        P_out = P.copy()
        if P_out._recursive:
            P_out._sumset = P._sumset | (Vs - G.An(Y))
        else:
            P_out._var = G.An(Y)
        
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

        return Probability(recursive=True, children=probabilities, sumset=Vs - (Y | X))

    if len(CCs) == 1:
        S = next(iter(CCs))

        # line 5
        if G.c_components == {Vs}:
            if verbose: print(f"[(ID) line 5]\tC(G): {G.c_components}    Vs: {Vs}")
            raise HedgeFound(G, G[S])
        
        # line 6
        if S in G.c_components:
            if verbose: print(f"[(ID) line 6]\tS: {S}    C(G): {G.c_components}")

            probabilities = set()
            for vertex in S:
                new_order = get_prev_orders(order, Vs)
                cond = set(new_order[:new_order.index(vertex)])
                P_out = get_new_probability(P, {vertex}, cond)
                probabilities.add(P_out)
            
            return Probability(recursive=True, children=probabilities, sumset=S - Y)
        
        # line 7
        for S_prime in G.c_components:
            if S < S_prime:
                if verbose: print(f"[(ID) line 7]\tS: {S}    S': {S_prime}")
                
                probabilities = set()
                for vertex in S_prime:
                    new_order = get_prev_orders(order, Vs)
                    prev = set(new_order[:new_order.index(vertex)])
                    # cond = (prev & S_prime) | (prev - S_prime)        # Equals to cond = prev 
                    P_out = get_new_probability(P, {vertex}, cond=prev)
                    probabilities.add(P_out)

                return myID(Y, X & S_prime, G[S_prime], 
                            Probability(recursive=True, children=probabilities, scope=S_prime), 
                            order, verbose, tab=tab + 1)


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
            if P_out._recursive:
                P_out._sumset = P._sumset | (Vs - Y)
            else:
                P_out._var = Y
            
            return P_out

    # line 3
    if Vs != G.An(Y):
        if verbose: print(f"[(gID) line 3]\tVs: {Vs}  G.An(Y): {G.An(Y)}")
        
        P_out = P.copy()
        if P_out._recursive:
            P_out._sumset = P._sumset | (Vs - G.An(Y))
        else:
            P_out._var = G.An(Y)

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
        
        return Probability(recursive=True, children=probabilities, sumset=Vs - (Y | X))
        
    # line 7
    for z in Z:
        if X >= z & Vs:
            if verbose: print(f"[(gID) line 7]\tX: {X}    Z∩V: {z & Vs}")

            P_out = P.copy()
            P_out._do = (z - Vs) | (X & z)
            P_out._var = Vs       # useless?
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
        if Q_out._recursive:
            Q_out._sumset = Q._sumset | (Vs - Y)
        else:
            Q_out._var = Y

        return Q_out

    # line 12
    if Vs != G.An(Y):
        if verbose: print(f"[(subID) line 12]\tVs: {Vs}  G.An(Y): {G.An(Y)}")
        
        Q_out = Q.copy()
        if Q_out._recursive:
            Q_out._sumset = Q._sumset | (Vs - G.An(Y))
        else:
            Q_out._var = G.An(Y)

        return mysubID(Y, X & G.An(Y), G[G.An(Y)], Q_out, order, verbose, tab=tab + 1)
    
    # line 13
    if (CCs:=G.c_components) == {Vs}:
        if verbose: print(f"[(subID) line 13]\tC(G): {G.c_components}    Vs: {Vs}")
        
        return None
    
    # line 14
    if S in CCs:
        if verbose: print(f"[(subID) line 14]\tS: {S}   C(G): {CCs}")
        
        probabilities = set()
        for vertex in Y:
            new_order = get_prev_orders(order, Vs)
            cond = set(new_order[:new_order.index(vertex)])
            Q_out = get_new_probability(Q, {vertex}, cond)
            probabilities.add(Q_out)
        
        return Probability(recursive=True, children=probabilities, sumset=S - Y)
    
    # line 15
    for S_prime in CCs:
        if S < S_prime:
            if verbose: print(f"[(subID) line 15]\tS: {S}   S': {S_prime}")

            probabilities = set()
            for vertex in S_prime:
                new_order = get_prev_orders(order, Vs)
                prev = set(new_order[:new_order.index(vertex)])
                Q_out = get_new_probability(Q, {vertex}, cond=prev)
                probabilities.add(Q_out)
            
            return mysubID(Y, X & S_prime, G[S_prime], 
                           Probability(recursive=True, children=probabilities, scope=S_prime), 
                           order, verbose, tab=tab + 1)


if __name__ == "__main__":

    G = CD({'X', 'W1', 'W2', 'W3', 'W4', 'W5', 'Y'}, 
                    [('X', 'Y'), ('W1', 'W2'), ('W2', 'X'), ('W4', 'X'), ('W3', 'W4')],
                    [('W1', 'W3', 'U_W1W3'), ('W2', 'W3', 'U_W2W3'), ('W3', 'W5', 'U_W3W5'), ('W4', 'W5', 'U_W4W5'), ('W1', 'Y', 'U_W1Y'), ('W1', 'X', 'U_W1X')])

    P = myID(Y={'Y'}, X={'X'}, G=G, verbose=True)
    print(f"ID: {P.printLatex()}")
    
    P1 = mygID(Y={'Y'}, X={'X'}, Z=[set()], G=G, verbose=True)
    print(f"gID: {P1.printLatex()}")