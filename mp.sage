from sage.combinat.species.generating_series import *
import sys

K = FractionField(PolynomialRing(QQ, "x"))
x = K.gen()

# note that here the variable T is always the set of subwords/subsequences
# that we want to find the distribution of.
# m is the size of T's alphabet 

# test to see if a set of words are reduced
def is_reduced(T):
    for t in T:
        for s in T - {t}:
            if t.find(s) != -1:
                return false
    return true

# the weighted adjacency matrix of the words, how they can cluster together
def wam(T, clusters):
    # if not is_reduced(set(T)):
    #     print("Patterns given aren't reduced")

    K = FractionField(PolynomialRing(QQ, x))
    mat = matrix(K, len(T)+1, len(T)+1, 0)

    # (-1) here is u_k in the paper
    for i in range(1, len(T)+1):
        mat[0,i] = (-1) * x^len(T[i-1])

    for pair in clusters:
        p, q = pair[0]
        i = T.index(p)
        j = T.index(q)
        # again here
        mat[i+1,j+1] += (-1)*x^(len(pair[1])-len(p))

    return mat

def mremoved(M, i, j):
    return M.delete_rows([i-1]).delete_columns([j-1])

def C(T, clusters):
    A = wam(T, clusters)
    I = identity_matrix(A.nrows())
    f = sum([(-1)^i * det(mremoved(I - A, i+1, 1)) for i in range(1, len(T)+1)])
    C = (1/det(I - A)) * f
    F = x + C
    return F

def sequence(expression, n):
    F = sum([factorial(m)*expression^m for m in range(n+1)])
    R = PowerSeriesRing(QQ,"x",default_prec=15)
    t = list(R(F))[1:n]
    try:
        return (tuple(t), oeis.find_by_subsequence(t, 1)[0].id())
    except:
        return (tuple(t), 'Not found')


def show_permutation(prm):
    return ''.join([str(d) for d in prm])

def show_equivalence(eq):
    return '\\equiv'.join([show_permutation(prm) for prm in eq])

def nub(seq):
    seen = set()
    seen_add = seen.add
    return [x for x in seq if not (x in seen or seen_add(x))]

def generate_latex(seq_dict):
    print('\\documentclass{article}')
    print('\\usepackage{amsmath}')
    print('\\usepackage{geometry}')
    print('\\usepackage{stackengine}')
    print('\\geometry{total={170mm,257mm}, left=20mm, top=20mm}')
    print('\\allowdisplaybreaks')
    print('\\begin{document}')
    
    for e in seq_dict:
        print('$$')
        print('\\begin{matrix}')
        exprs = []
        for _, _, _, _, expr, _ in seq_dict[e]:
            exprs.append(expr)

        for express in nub(exprs):
            print('\\sum_{m \geq 0} m! \\left(')
            print(latex(express))
            print('\\right)^m')

        seq, name = e
        print(latex(seq))
        print('\\texttt{')
        print(name)
        print('}')
        print('\\end{matrix}')
        print('$$')
        print('\\begin{align}')
        for i, d in enumerate(seq_dict[e]):
            equivs, R, domain, clusters, expr, match = d
            if match:
                print('\\text{RRR}')
            else:
                print('\\text{VVV}')

            print('\\quad')

            for j in range(0, len(equivs)):
                print(show_equivalence(equivs[j]))
                print('\\quad')
            print('&')
            print('\\begin{matrix}')
            for j in range(0, len(R)):
                print(R[j])
                if j != len(R) - 1:
                    print('\\\\')
            print('\\end{matrix}')

            if i != len(seq_dict[e]) - 1:
                print('\\\\')

        print('\\end{align}')

    print('\\end{document}')

verify_data = {}
for line in open('verify_data', 'r'):
    equivs, seq = eval(line)
    verify_data[str(equivs)] = seq

master = {}
for line in sys.stdin:
    t = eval(line)
    equivs, system, domain, clusters = t
    expr = C(domain, clusters)
    s = sequence(expr, 8)
    match = False
    try:
        ver_seq = verify_data[str(equivs)]
        match = tuple(ver_seq) == s[0][0:6]
    except KeyError:
        pass
        
    u = (equivs, system, domain, clusters, expr, match)
    if s not in master:
        master[s] = [u]
    else:
        master[s].append(u)

generate_latex(master)

#for line in sys.stdin:
#    equivs, R, domain, clusters = eval(line)
#    print(sequence(domain, clusters, 8))

