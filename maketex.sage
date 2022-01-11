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
    return (1/det(I - A)) * f

def sequence(xclustergf, n):
    F = sum([factorial(m)*xclustergf^m for m in range(n+1)])
    R = PowerSeriesRing(QQ,"x",default_prec=15)
    t = list(R(F))[1:n]
    try:
        return (tuple(t), oeis.find_by_subsequence(t, 1)[0].id())
    except:
        return (tuple(t), 'Not present')


def show_permutation(prm):
    return ''.join([str(d) for d in prm])

def show_rule(rule):
    target, result = rule
    return show_permutation(target) + ' \\to ' + show_permutation(result)

def show_equivalence(eq):
    return '\{' + ', '.join([show_permutation(prm) for prm in eq]) + '\}'
 
def equivalence_size(eqs):
    return sum([len(eq)-1 for eq in eqs])

def nub(seq):
    seen = set()
    seen_add = seen.add
    return [x for x in seq if not (x in seen or seen_add(x))]

def generate_latex(seq_dict):
    sys.stdout = open('appendix.tex', 'w')
    rawfile = open('appendix.raw', 'w')
    
    print('\\allowdisplaybreaks')
    print('\\begin{tiny}')
    
    for e in seq_dict:
        print('$$')
        print('\\begin{matrix}')
        exprs = []
        for _, _, _, _, xclustergf, clustergf in seq_dict[e]:
            exprs.append((xclustergf, clustergf))

        for xcgf, cgf in nub(exprs):
            print('\\sum_{m \geq 0} m! \\left(')
            print(latex(xcgf))
            print('\\right)^m')

            print('\\ ')
            print(latex(cgf))

        print('\\\\')

        seq, name = e
        print(latex(list(seq) + ['...']))
        print('\\ ')
        print('\\texttt{' + name + '}')
        print('\\end{matrix}')
        print('$$')

        print('\\vspace{-1em}')

        print('\\begin{align}')
        for i, d in enumerate(seq_dict[e]):
            equivs, R, domain, clusters, _, _ = d

            print((equivs, list(seq)), file=rawfile)

            if equivs == []:
                print('\\textnormal{the identity equivalence}')
                continue

            print('\{' + ', '.join([show_equivalence(e) for e in equivs]) + '\}')
            print('\\quad')
            
            print('&')

            print('\\begin{matrix}')
            print('\\\\'.join([show_rule(r) for r in R]))
            print('\\end{matrix}')

            if i == len(seq_dict[e]) - 1:
                break

            print('\\\\')

        print('\\end{align}')
    print('\\end{tiny}')

master = {}
for line in sys.stdin:
    t = eval(line)
    equivs, system, domain, clusters = t
    clustergf = C(domain, clusters)
    xclustergf = x + clustergf

    s = sequence(xclustergf, 8)
    u = (equivs, system, domain, clusters, xclustergf, clustergf)
    if s not in master:
        master[s] = [u]
    else:
        master[s].append(u)

generate_latex(master)

