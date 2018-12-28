import sys
import sexp
import pprint
import random
import translator
from z3 import *

string2pythonOperator = {
    "+": lambda x, y: x + y,
    "-": lambda x, y: x - y,
    "*": lambda x, y: x * y,
    "div": lambda x, y: x // y,
    "mod": lambda x, y: x % y,
    "ite": lambda b, x, y: x if b else y,
    "=": lambda x, y: x == y,
    "<=": lambda x, y: x <= y,
    ">=": lambda x, y: x >= y,
    "<": lambda x, y: x < y,
    ">": lambda x, y: x > y
}

def stripComments(bmFile):
    noComments = '('
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + ')'


def getId(type, id):
    return type + str(id)


def declareVar(type, id, VarTable):
    newVar = translator.DeclareVar(type, id)
    # print "declareVar", id, newVar, type
    VarTable[str(newVar)] = newVar
    return newVar


def replaceFunctionCall(Term, functionCallDic, functionName, outputType, VarTable):
    if not type(Term) == list:
        if type(Term) == tuple:
            return [[], str(Term[1])]
        else:
            return [[], Term]
    resTerm = [[], []]
    for term in Term:
        if type(term) == list and term[0] == functionName:
            newArguments = []
            for arg in term[1:]:
                subCall, subTerm = replaceFunctionCall(arg, functionCallDic, functionName, outputType, VarTable)
                for call in subCall:
                    if call not in resTerm[0]:
                        resTerm[0].append(call)
                newArguments.append(subTerm)
            # print newArguments
            if str(newArguments) in functionCallDic:
                functionCallVar = functionCallDic[str(newArguments)][0]
                resTerm[0].append(str(functionCallVar))
                resTerm[1].append(str(functionCallVar))
            else:
                id = len(functionCallDic)
                currentOutput = declareVar(outputType, "functionCall%d"%(id), VarTable)
                functionCallDic[str(newArguments)] = [currentOutput, newArguments]
                if str(currentOutput) not in resTerm[0]:
                    resTerm[0].append(str(currentOutput))
                resTerm[0].append(str(currentOutput))
                resTerm[1].append(str(currentOutput))
        elif type(term) == list:
            subCall, subTerm = replaceFunctionCall(term, functionCallDic, functionName, outputType, VarTable)
            for call in subCall:
                if call not in resTerm[0]:
                    resTerm[0].append(call)
            resTerm[1].append(subTerm)
        else:
            resTerm[1].append(term)
    return resTerm


def replaceCons(Cons, s1, s2):
    if type(Cons) != list:
        if Cons == s1:
            return s2
        return Cons
    return list(map(lambda x: replaceCons(x, s1, s2), Cons))


def simplifyOperator(Operators):
    simpleOperators = []
    # print(Operators)
    for operatorType in Operators:
        isBool = operatorType[1] == 'Bool'
        isInt = operatorType[1] == 'Int'
        # print(operatorType)
        for arg in operatorType[2]:
            if arg != ['Bool']:
                isBool = False
            if arg != ['Int']:
                isInt = False
        if isBool:
            continue
        resultOperator = []
        for operator in operatorType[0]:
            if operator == '<' and '>' in resultOperator: continue
            if operator == '>' and '<' in resultOperator: continue
            if operator == '<=' and '>=' in resultOperator: continue
            if operator == '>=' and '<=' in resultOperator: continue
            resultOperator.append(operator)
        simpleOperators.append([resultOperator] + operatorType[1:])
    return simpleOperators


def replaceTerm(term, s, t):
    resultTerm = []
    if term == s:
        return t
    if type(term) != list:
        return term
    for subTerm in term:
        resultTerm.append(replaceTerm(subTerm, s, t))
    return resultTerm


def dfsGetPossibleValueCons(currentSet, functionCalls, Args, VarTable, currentFunctionCall, ReplacedCons):
    if len(functionCalls) == 0:
        spec = "\n".join(list(map(lambda x: "(assert %s)"%(translator.toString(x[1:])), ReplacedCons)))
        result = parse_smt2_string(spec, decls=VarTable)
        return [Not(And(result))]
    functionVar, functionArgs = functionCalls[0]
    if str(functionVar) not in currentFunctionCall:
        return dfsGetPossibleValueCons(currentSet, functionCalls[1:], Args, VarTable, currentFunctionCall, ReplacedCons)
    result = []
    for value in currentSet:
        newTerm = value
        for i in range(len(Args)):
            newTerm = replaceTerm(newTerm, Args[i][0], functionArgs[i])
        result += dfsGetPossibleValueCons(currentSet, functionCalls[1:], Args, VarTable, currentFunctionCall,
                                          list(map(lambda x: replaceTerm(x, str(functionVar), newTerm), ReplacedCons)))
    return result



def isValueSetFull(currentSet, functionCallDic, ArgumentDict, VarTable, ReplacedConsSet):
    solver = Solver()
    functionCallInfo = [functionCallDic[i] for i in functionCallDic]
    allCons = []
    for ReplacedCons in ReplacedConsSet:
        allCons.append(And(dfsGetPossibleValueCons(currentSet, functionCallInfo, ArgumentDict, VarTable,
                                                   ReplacedCons[0], ReplacedCons[1])))
    solver.add(Or(allCons))
    # print(solver)
    # print(solver.check())
    return solver.check() == unsat


def simplifyResultSet(resultSet, superSet, functionCallDic, ArgumentDict, VarTable, ReplacedConsSet):
    #print(len(resultSet), len(superSet))
    if isValueSetFull(superSet, functionCallDic, ArgumentDict, VarTable, ReplacedConsSet):
        return []
    if len(resultSet) == 1:
        return resultSet
    middle = len(resultSet) // 2
    leftSet = resultSet[: middle]
    rightSet = resultSet[middle:]
    left = simplifyResultSet(leftSet, superSet + rightSet, functionCallDic, ArgumentDict, VarTable, ReplacedConsSet)
    right = simplifyResultSet(rightSet, superSet + left, functionCallDic, ArgumentDict, VarTable, ReplacedConsSet)
    return left + right


def getConsSet(ConsInfo):
    functionCallDic = {}
    functionCallId = 1
    loc = [0]
    consSet =[[[],[]]]
    # pprint.pprint(ConsInfo)
    for consInfo in ConsInfo:
        for functionName in consInfo[0]:
            if not functionName in functionCallDic:
                functionCallDic[functionName] = functionCallId
                loc.append(functionCallId)
                consSet.append([[functionName], []])
                functionCallId += 1

    for functionCalls, Cons in ConsInfo:
        location = 0
        if len(functionCalls) > 0:
            location = loc[functionCallDic[functionCalls[0]]]
            for functionCall in functionCalls:
                where = loc[functionCallDic[functionCall]]
                if where != location:
                    consSet[location][0].extend(consSet[where][0])
                    consSet[location][1].extend(consSet[where][1])
                    for functionName in consSet[where][0]:
                        loc[functionCallDic[functionName]] = location
                    consSet[where] = [[], []]
        consSet[location][1].append(Cons)

    result = []
    for cons in consSet:
        if len(cons[1]) > 0:
            result.append(cons)
    return result


def chcekMerge(operator, lTerm, rTerm):
    if operator in ['mod', 'div']:
        if type(rTerm) != str:
            return False
        try:
            int(rTerm)
        except:
            return False
        return True
    return True


class ValueSet:
    def __init__(self, argVarTable, Samples, Operators):
        self.VarTable = argVarTable
        self.Samples = Samples
        self.Operators = Operators
        self.hashTable = {}
        self.Value = [[]]

    def get(self, depth):
        while len(self.Value) <= depth:
            self.extendValue()
        return self.Value[depth]

    def addNewValue(self, var, depth):
        resultVar = self.VarTable["__result"]
        spec = "(assert (= %s %s))"%(str(resultVar), translator.toString(var))
        result = parse_smt2_string(spec, decls=self.VarTable)

        solver = Solver()
        solver.add(result)

        sampleOutput = []
        for sample in self.Samples:
            solver.push()
            for arg in self.VarTable:
                if arg in sample:
                    solver.add(self.VarTable[arg] == sample[arg])
            solver.check()
            model = solver.model()
            sampleOutput.append(model[resultVar].as_long())
            solver.pop()

        hashIndex = str(sampleOutput)
        if hashIndex not in self.hashTable:
            self.hashTable[hashIndex] = []
        else:
            for otherVar in self.hashTable[hashIndex]:
                solver.push()
                spec = "(assert (not (= %s %s)))"%(str(resultVar), translator.toString(otherVar))
                solver.add(parse_smt2_string(spec, decls=self.VarTable))
                if solver.check() == unsat:
                    return False
                solver.pop()

        #print(var)
        self.hashTable[hashIndex].append(var)
        self.Value[depth].append(var)
        return True

    def extendValue(self):
        depth = len(self.Value)
        self.Value.append([])
        for operatorType in self.Operators:
            resultType = operatorType[1]
            argument = operatorType[2]
            if len(argument) != 2 or resultType != 'Int': continue
            for lsize in range(depth):
                for rsize in range(depth - lsize):
                    for operator in operatorType[0]:
                        for lTerm in self.Value[lsize]:
                            for rTerm in self.Value[rsize]:
                                if not chcekMerge(operator, lTerm, rTerm): continue
                                self.addNewValue([operator, lTerm, rTerm], depth)


def getPossibleValue(Operators, Expr, Terminals):
    SynFunExpr, VarTable, FunDefMap, Constraints = translator.ReadQuery(Expr)
    returnType = SynFunExpr[3]

    functionCallDic = {}
    ReplacedConsInfo = []
    for i in range(len(Constraints)):
        ReplacedConsInfo.append(replaceFunctionCall(Constraints[i], functionCallDic, SynFunExpr[1], SynFunExpr[3], VarTable))
    ReplacedConsSet = getConsSet(ReplacedConsInfo)
    # pprint.pprint(ReplacedConsSet)

    resultSet = []
    argVarTable = {}
    for arg in SynFunExpr[2]:
        declareVar(arg[1], arg[0], argVarTable)

    Samples = []
    sampleNum = 30
    for _ in range(sampleNum):
        sample = {}
        for arg in SynFunExpr[2]:
            value = False
            if arg[1] == 'Bool':
                value = random.randint(0, 1) == 0
            else:
                value = random.randint(0, 100)
            sample[arg[0]] = value
        Samples.append(sample)
    Value = ValueSet(argVarTable, Samples, Operators)

    if returnType == 'Bool':
        resultSet = ['true', 'false']
    else:
        depth = 0
        argVarTable["__result"] = Int("__result")
        for terminal in Terminals['Int']:
            Value.addNewValue(terminal, depth)
        #print(Value)
        while True:
            resultSet += Value.get(depth)
            #print(resultSet)
            if isValueSetFull(resultSet, functionCallDic, SynFunExpr[2], VarTable, ReplacedConsSet):
                break
            depth += 1

    resultSet = simplifyResultSet(resultSet, [], functionCallDic, SynFunExpr[2], VarTable, ReplacedConsSet)
    return resultSet, Value


def getCodeFromTermInfo(TermInfo):
    condition, value = TermInfo[0]
    if len(TermInfo) == 1 or len(condition) == 0:
        return value
    return ["ite", condition, value, getCodeFromTermInfo(TermInfo[1:])]


def getCode(TermInfo, SynFunExpr):
    code = getCodeFromTermInfo(TermInfo)
    FuncDefineStr = '(define-fun'
    for i in range(1, 4):
        currentStr = translator.toString(SynFunExpr[i])
        if i == 2 and len(SynFunExpr[i]) == 1:
            currentStr = "(%s)" % (currentStr)
        FuncDefineStr += " " + currentStr
    FuncDefineStr += ")"
    fullResultCode = FuncDefineStr[:-1] + ' ' + translator.toString(code) + FuncDefineStr[-1]
    return fullResultCode


class BoolTable:
    def __init__(self, VarTable, VarList, Values, Operators):
        self.VarTable = VarTable
        self.Cons = []
        self.TreeTable = []
        self.Root = -1
        self.VarList = VarList
        self.Values = Values
        self.Operators = Operators

    def parseVar(self, var, sample):
        if type(var) == str:
            if var in self.VarTable:
                result = sample[self.VarTable[var]]
                if result is None:
                    if is_int(self.VarTable[var]):
                        return 0
                    else:
                        return True
                if is_int(result):
                    return result.as_long()
                else:
                    return is_true(result)
            return int(var)
        if len(var) == 3:
            return string2pythonOperator[var[0]](self.parseVar(var[1], sample), self.parseVar(var[2], sample))
        else:
            return string2pythonOperator[var[0]](self.parseVar(var[1], sample), self.parseVar(var[2], sample),
                                                 self.parseVar(var[3], sample))

    def getValue(self, var, sample):
        return self.parseVar(var, sample)

    def checkEq(self, var1, var2):
        solver = Solver()
        spec = "(assert (xor %s %s))"%(translator.toString(var1), translator.toString(var2))
        solver.add(parse_smt2_string(spec, decls=self.VarTable))
        result = solver.check()
        if result == sat:
            return [False, solver.model()]
        else:
            return [True, None]

    def insert(self, var, depth):
        if self.Root == -1:
            self.Root = 0
            self.TreeTable.append(var)
            self.Cons[depth].append(var)
            return
        currentNode = self.Root
        while type(self.TreeTable[currentNode][0]) != str:
            sample, lNode, rNode = self.TreeTable[currentNode]
            if self.getValue(var, sample):
                currentNode = lNode
            else:
                currentNode = rNode
        result, newSample = self.checkEq(var, self.TreeTable[currentNode])
        # print(result, newSample)
        if result: return
        lId = len(self.TreeTable)
        rId = len(self.TreeTable) + 1
        if self.getValue(var, newSample):
            self.TreeTable.append(var)
            self.TreeTable.append(self.TreeTable[currentNode])
        else:
            self.TreeTable.append(self.TreeTable[currentNode])
            self.TreeTable.append(var)
        self.TreeTable[currentNode] = [newSample, lId, rId]
        self.Cons[depth].append(var)

    def extendCons(self):
        depth = len(self.Cons)
        self.Cons.append([])
        for operatorType in self.Operators:
            isAllInt = True
            for argType in operatorType[2]:
                if argType != ['Int']:
                    isAllInt = False
            if (not isAllInt) or operatorType[1] != 'Bool':
                continue
            for operator in operatorType[0]:
                for lsize in range(depth + 1):
                    rsize = depth - lsize
                    for lTerm in self.Values.get(lsize):
                        for rTerm in self.Values.get(rsize):
                            # print("tryInsert", [operator, lTerm, rTerm])
                            ConsTable.insert([operator, lTerm, rTerm], depth)

    def getCons(self, depth):
        while len(self.Cons) <= depth:
            self.extendCons()
        return self.Cons[depth]

    def filter(self, depth, example):
        result = []
        for i in range(depth+1):
            for cons in self.getCons(i):
                if self.getValue(cons, example):
                    result.append(cons)
        return result


def reformatListCons(Cons):
    if len(Cons) == 0:
        return []
    result = [Cons[0]]
    for cons in Cons[1:]:
        result = ["and", result, cons]
    return result


def replaceArgs(Term, argList, functionArg):
    newTerm = Term
    for i in range(len(argList)):
        newTerm = replaceTerm(newTerm, argList[i][0], functionArg[i])
    return newTerm


def checkValid(solver, newCons, VarTable, argList, functionArg):
    solver.push()
    if len(newCons) > 0:
        spec = "(assert %s)" % (translator.toString(reformatListCons(replaceArgs(newCons, argList, functionArg))))
        # print(spec)
        solver.add(parse_smt2_string(spec, decls=VarTable))
    result = solver.check()
    # print(result)
    solver.pop()
    if result == unsat:
        return True
    return False


def reduceCons(solver, currentCons, Super, VarTable, argList, functionArg):
    if checkValid(solver, Super, VarTable, argList, functionArg):
        return []
    if len(currentCons) == 1:
        return currentCons
    middle = len(currentCons) // 2
    leftCons = currentCons[: middle]
    rightCons = currentCons[middle:]
    leftRes = reduceCons(solver, leftCons, Super + rightCons, VarTable, argList, functionArg)
    return leftRes + reduceCons(solver, rightCons, Super + leftRes, VarTable, argList, functionArg)


def getTermCondition(Expr, TermInfo, currentTerm, RemainTerms, ConsTable, VarTable):
    SynFunExpr, VarTable, FunDefMap, Constraints = translator.ReadQuery(Expr)

    functionCallDic = {}
    ReplacedConsInfo = []
    for i in range(len(Constraints)):
        ReplacedConsInfo.append(
            replaceFunctionCall(Constraints[i], functionCallDic, SynFunExpr[1], SynFunExpr[3], VarTable))
    ReplacedConsSet = getConsSet(ReplacedConsInfo)
    assert len(ReplacedConsSet) == 1 and len(ReplacedConsSet[0][0]) == 1
    print(VarTable)

    ReplacedCons = ReplacedConsSet[0][1]
    # print(functionCallDic)
    functionCallVar = None
    functionArgs = None
    for functionCallId in functionCallDic:
        functionCallVar, functionArgs = functionCallDic[functionCallId]
    # print(functionCallVar, functionArgs)

    exampleGenerator = Solver()
    checkSolver = Solver()
    for condition, term in TermInfo:
        spec = "(assert (not %s))"%(translator.toString(replaceArgs(condition, SynFunExpr[2], functionArgs)))
        spec = parse_smt2_string(spec, decls=VarTable)
        exampleGenerator.add(spec)
        checkSolver.add(spec)
    for term in RemainTerms:
        spec = "(assert (not (= %s %s)))"%(str(functionCallVar), replaceArgs(term, SynFunExpr[2], functionArgs))
        exampleGenerator.add(parse_smt2_string(spec, decls=VarTable))
    spec = "(assert (= %s %s))"%(str(functionCallVar), replaceArgs(currentTerm, SynFunExpr[2], functionArgs))
    spec = parse_smt2_string(spec, decls=VarTable)
    exampleGenerator.add(spec)
    checkSolver.add(spec)
    spec = "\n".join(list(map(lambda x: "(assert %s)" % (translator.toString(x[1:])), ReplacedCons)))
    spec = parse_smt2_string(spec, decls=VarTable)
    exampleGenerator.add(spec)
    checkSolver.add(Not(And(spec)))
    # print(checkSolver)

    depth = 0
    result = []
    while True:
        exampleResult = exampleGenerator.check()
        if exampleResult == unsat:
            break
        example = exampleGenerator.model()
        suitableCons = ConsTable.filter(depth, example)
        print(example)
        if not checkValid(checkSolver, suitableCons, VarTable, SynFunExpr[2], functionArgs):
            depth += 1
            continue
        reducedCondition = reduceCons(checkSolver, suitableCons, [], VarTable, SynFunExpr[2], functionArgs)
        reducedCondition = reformatListCons(reducedCondition)
        print(reducedCondition)
        input()
        if len(reducedCondition) > 0:
            if len(result) == 0:
                result = reducedCondition
            else:
                result = ["or", result, reducedCondition]
            spec = "(assert (not %s))"%(translator.toString(replaceArgs(reducedCondition, SynFunExpr[2], functionArgs)))
            exampleGenerator.add(parse_smt2_string(spec, decls=VarTable))
        else:
            return []

    return result


if __name__ == '__main__':
    benchmarkFile = open(sys.argv[1])
    #benchmarkFile = open("../../tests/open_tests/max6.sl")
    bm = stripComments(benchmarkFile)
    # print(bm)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0] #Parse string to python list
    #print (checker.check('(define-fun f ((x Int)) Int (mod (* x 3) 10)  )'))
    #raw_input()
    SynFunExpr = []
    StartSym = 'My-Start-Symbol' #virtual starting symbol
    for expr in bmExpr:
        if len(expr)==0:
            continue
        elif expr[0]=='synth-fun':
            SynFunExpr=expr
    FuncDefine = ['define-fun']+SynFunExpr[1:4] #copy function signature
    Productions = {StartSym:[]}
    ReturnType = SynFunExpr[3]
    Type = {StartSym:SynFunExpr[3]} # set starting symbol's return type
    Terminals = {'Int':[], 'Bool':[]}
    Operators = []

    for NonTerm in SynFunExpr[4]: #SynFunExpr[4] is the production rule
        NTName = NonTerm[0]
        NTType = NonTerm[1]
        assert NTType in ['Int', 'Bool']
        if NTType == Type[StartSym]:
            Productions[StartSym].append(NTName)
        Type[NTName] = NTType
        #Productions[NTName] = NonTerm[2]
        Productions[NTName] = []
        for NT in NonTerm[2]:
            if type(NT) == tuple:
                Productions[NTName].append(str(NT[1])) # deal with ('Int',0). You can also utilize type information, but you will suffer from these tuples.
            else:
                Productions[NTName].append(NT)

    SynFunExpr, VarTable, _, Constraints, checker = translator.ReadQuery(bmExpr, True)

    operatorTable = {}
    for NonTerm in SynFunExpr[4]:
        for NT in NonTerm[2]:
            current = NT
            if type(NT) == tuple:
                current = str(NT[1])
            if type(current) == str:
                if current not in Type and current not in Terminals[NonTerm[1]]:
                    Terminals[NonTerm[1]].append(current)
            else:
                operatorArgs = []
                for i in NT[1:]:
                    if i in Type:
                        operatorArgs.append([Type[i]])
                    else:
                        operatorArgs.append(i)
                operatorStr = str([NonTerm[1], operatorArgs])
                if operatorStr in operatorTable:
                    operatorLoc = operatorTable[operatorStr]
                    Operators[operatorLoc][0].append(NT[0])
                else:
                    operator = [[NT[0]], NonTerm[1]]
                    operator.append(operatorArgs)
                    operatorTable[operatorStr] = len(Operators)
                    Operators.append(operator)
    Operators = simplifyOperator(Operators)
    # print(Terminals)
    #print(Operators)

    PossibleTerm, Values = getPossibleValue(Operators, bmExpr, Terminals)
    if len(PossibleTerm) == 1:
        print(getCode([[[], PossibleTerm[0]]], SynFunExpr))
        exit(0)

    argVarTable = {}
    for arg in SynFunExpr[2]:
        declareVar(arg[1], arg[0], argVarTable)
    argVarTable["__result"] = Bool("__result")

    TermInfo = []
    ConsTable = BoolTable(argVarTable, SynFunExpr[2], Values, Operators)
    for i in range(len(PossibleTerm)):
        term = PossibleTerm[i]
        TermInfo.append([getTermCondition(bmExpr, TermInfo, term, PossibleTerm[i+1:], ConsTable, VarTable), term])

    resultCode = getCode(TermInfo, SynFunExpr)
    print(resultCode)
    print(checker.check(resultCode))