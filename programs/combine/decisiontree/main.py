import sys

from decisiontree.possibleterm.possibleterm import findPossibleValue
from decisiontree.semantics.semantics import exprFromList
from decisiontree.instrument.task import SynthTask
from decisiontree.decisiontree.treelearning import TreeLearner, genmoreconstraint


def main(return_dict):
    task = SynthTask(sys.argv[1])
    if task.ins is task.ori:
        return_dict["decisiontree"] = "invalid"
        return
    possiblevalue = list(map(lambda l: exprFromList(l, [task.functionProto]),
                             findPossibleValue(task.ins.bmExpr)))
    moreconstraint = genmoreconstraint(task.productions, task.ins.inputlist, task.ins.inputtylist)
    treelearner = TreeLearner(task.ins.semchecker, task.ins.z3checker, possiblevalue, moreconstraint)
    expr = treelearner.mainalgo()
    task.functionProto.expr = expr
    return_dict["decisiontree"] = str(task.functionProto)
    #print(treelearner.mainalgo())
    #expr = Expr('ite', Expr('>=', Expr('x'), Expr('y')), Expr('x'), Expr('y'))
    #print(sem.check(expr, {'x': 1, 'y': 2}))
    #expr = Expr('ite', Expr('<=', Expr('x'), Expr('y')), Expr('x'), Expr('y'))
    #print(sem.check(expr, {'x': 1, 'y': 2}))



if __name__ == '__main__':
    return_dict = dict()
    main(return_dict)
    print(return_dict["decisiontree"])


