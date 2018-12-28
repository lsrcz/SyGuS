import sys

from task import SynthTask
from treelearning import TreeLearner


def main():
    task = SynthTask(sys.argv[1])
    treelearner = TreeLearner(task.ins.semchecker, task.ins.z3checker)
    print(treelearner.mainalgo())
    #expr = Expr('ite', Expr('>=', Expr('x'), Expr('y')), Expr('x'), Expr('y'))
    #print(sem.check(expr, {'x': 1, 'y': 2}))
    #expr = Expr('ite', Expr('<=', Expr('x'), Expr('y')), Expr('x'), Expr('y'))
    #print(sem.check(expr, {'x': 1, 'y': 2}))



if __name__ == '__main__':
    main()


