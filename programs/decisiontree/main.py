from fileinput import readin, getZ3checker, getProductions, getSemChecker
from semantics import Expr
from treelearning import TreeLearner
import sys


def main():
    bm = readin(sys.argv[1])
    productions, func = getProductions(bm)
    Expr.productions = productions
    z3checker = getZ3checker(bm)
    sem = getSemChecker(bm, func)
    treelearner = TreeLearner(sem, z3checker)
    print(treelearner.mainalgo())
    #expr = Expr('ite', Expr('>=', Expr('x'), Expr('y')), Expr('x'), Expr('y'))
    #print(sem.check(expr, {'x': 1, 'y': 2}))
    #expr = Expr('ite', Expr('<=', Expr('x'), Expr('y')), Expr('x'), Expr('y'))
    #print(sem.check(expr, {'x': 1, 'y': 2}))



if __name__ == '__main__':
    main()


