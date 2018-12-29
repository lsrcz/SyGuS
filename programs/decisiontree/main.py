import sys

from possibleterm import findPossibleValue
from semantics import exprFromList
from task import SynthTask
from treelearning import TreeLearner


def main():
    task = SynthTask(sys.argv[1])
    possiblevalue = list(map(lambda l: exprFromList(l, task.functionProto),
                             findPossibleValue(task.ins.bmExpr)))
    treelearner = TreeLearner(task.ins.semchecker, task.ins.z3checker, possiblevalue)
    print(treelearner.mainalgo())
    #expr = Expr('ite', Expr('>=', Expr('x'), Expr('y')), Expr('x'), Expr('y'))
    #print(sem.check(expr, {'x': 1, 'y': 2}))
    #expr = Expr('ite', Expr('<=', Expr('x'), Expr('y')), Expr('x'), Expr('y'))
    #print(sem.check(expr, {'x': 1, 'y': 2}))



if __name__ == '__main__':
    main()


