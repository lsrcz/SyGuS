import sys
import sexp
import pprint
import random
import translator
from z3 import *


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
            return str(Term[1])
        else:
            return Term
    resTerm = []
    for term in Term:
        if type(term) == list and term[0] == functionName:
            newArguments = []
            for arg in term[1:]:
                newArguments.append(replaceFunctionCall(arg, functionCallDic, functionName, outputType, VarTable))
            # print newArguments
            if str(newArguments) in functionCallDic:
                resTerm.append(str(functionCallDic[str(newArguments)][0]))
            else:
                id = len(functionCallDic)
                currentOutput = declareVar(outputType, "functionCall%d"%(id), VarTable)
                functionCallDic[str(newArguments)] = [currentOutput, newArguments]
                resTerm.append(str(currentOutput))
        elif type(term) == list:
            resTerm.append(replaceFunctionCall(term, functionCallDic, functionName, outputType, VarTable))
        else:
            resTerm.append(term)
    return resTerm


def replaceCons(Cons, s1, s2):
    if type(Cons) != list:
        if Cons == s1:
            return s2
        return Cons
    return list(map(lambda x: replaceCons(x, s1, s2), Cons))


def getCode(operatorId, model, Operators, InputVar, OutputVarTable, Terminals, OperatorTypeVar):
    operator = Operators[operatorId]
    result = [operator[0][model[OperatorTypeVar[operatorId]].as_long()]]
    inputId = -1
    for term in operator[2:]:
        if type(term) == list:
            inputId += 1
            inputVar = InputVar[operatorId][inputId]
            inputType = term[0]
            inputLoc = model[inputVar].as_long()
            if inputLoc < len(Terminals[inputType]):
                result.append(Terminals[inputType][inputLoc])
            else:
                sonOperator = OutputVarTable[inputLoc]
                result.append(getCode(sonOperator, model, Operators, InputVar,
                                      OutputVarTable, Terminals, OperatorTypeVar))
        else:
            result.append(term)
    return result

def trySolve(Terminals, Operators, ReturnType, bmExpr):
    # print(Operators)
    InputVar = []
    OutputVar = []
    OperatorTypeVar = []
    TypeNumber = {'Bool': 0, 'Int': 0}
    MidNumber = max(len(Terminals['Bool']), len(Terminals['Int']))
    StartNumber = MidNumber
    SynFunExpr, VarTable, FunDefMap, Constraints = translator.ReadQuery(bmExpr)
    inputVars = list(VarTable.keys())
    inputVarTable = VarTable.copy()
    qualityCons = []
    for i in range(len(inputVars)):
        x = VarTable[inputVars[i]]
        qualityCons.append(x > 4)
        for j in range(len(inputVars)):
            if i != j:
                y = VarTable[inputVars[j]]
                qualityCons.append(x > y + 4)
    random.shuffle(qualityCons)

    for operator in Operators:
        outputType = operator[1]
        OutputVar.append(declareVar('Int', getId(outputType, TypeNumber[outputType]), VarTable))
        TypeNumber[outputType] += 1
        MidNumber += 1
        currentInputVar = []
        for arg in operator[2:]:
            if type(arg) == list:
                inputType = arg[0]
                currentInputVar.append(declareVar('Int', getId(inputType, TypeNumber[inputType]), VarTable))
                TypeNumber[inputType] += 1
        InputVar.append(currentInputVar)
    resultVar = declareVar('Int', getId(ReturnType, TypeNumber[ReturnType]), VarTable)
    TypeNumber[ReturnType] += 1

    s1 = Solver()
    s2 = Solver()
    s3 = Solver()

    functionCallDic = {}
    ReplacedCons = []
    for i in range(len(Constraints)):
        ReplacedCons.append(replaceFunctionCall(Constraints[i], functionCallDic, SynFunExpr[1], SynFunExpr[3], VarTable))
    spec = "\n".join(list(map(lambda x: "(assert %s)"%translator.toString(x[1:]), ReplacedCons)))
    spec = parse_smt2_string(spec, decls=VarTable)
    s1.add(spec)

    inputQualityCons = []
    for constraint in qualityCons:
        inputQualityCons.append(constraint)
        s1.push()
        s1.add(And(inputQualityCons))
        currentRes = s1.check()
        s1.pop()
        if currentRes == unsat:
            inputQualityCons = inputQualityCons[:-1]

    s1.push()
    s1.add(inputQualityCons)
    s1.check()
    currentModel = s1.model()
    s1.pop()
    Models = []
    s1 = Solver()

    ArgumentDict = {}
    # print(Terminals)
    argId = -1
    for arg in SynFunExpr[2]:
        argId += 1
        ArgumentDict[arg[0]] = argId

    SimplifyOption = False
    for operator in Operators:
        if '+' or '-' in operator[0] and "0" in Terminals['Int']:
            SimplifyOption = True
        if '*' or '/' or 'div' in operator[0] and "1" in Terminals['Int']:
            SimplifyOption = True

    for i in range(len(Operators)):
        OperatorTypeVar.append(declareVar('Int', getId("operatorType", i), VarTable))
        outputVar = OutputVar[i]
        operator = Operators[i]
        operatorTypeVar = OperatorTypeVar[i]
        s3.add(outputVar >= StartNumber)
        s3.add(outputVar < MidNumber)
        s3.add(operatorTypeVar >= 0)
        s3.add(operatorTypeVar < len(operator[0]))
        for inputVar in InputVar[i]:
            s3.add(outputVar > inputVar)
            if 'Bool' in str(inputVar):
                currentInputType = 'Bool'
            else:
                currentInputType = 'Int'
            if SimplifyOption and currentInputType == 'Int' and operator[1] == 'Bool':
                # print(operator)
                currentCons = []
                terminalId = -1
                for terminal in Terminals['Int']:
                    terminalId += 1
                    try:
                        int(terminal)
                    except:
                        # print(terminal)
                        currentCons += [inputVar == terminalId]
            else:
                currentCons = [And(inputVar >= 0, inputVar < len(Terminals[currentInputType]))]
            for j in range(len(Operators)):
                if Operators[j][1] == currentInputType:
                    currentCons.append(inputVar == OutputVar[j])
            s3.add(Or(currentCons))
    currentCons = []
    for i in range(len(Operators)):
        if Operators[i][1] == ReturnType:
            currentCons.append(resultVar == OutputVar[i])
    # print "fin ", currentCons
    s3.add(Or(currentCons))
    for i in range(len(Operators)):
        for j in range(i+1, len(Operators)):
            s3.add(OutputVar[i] != OutputVar[j])
    # print(Operators)
    # print(Terminals)
    # print(MidNumber)
    # print len(Terminals['Int']), len(Terminals['Bool'])
    # print(inputQualityCons)
    # print(Models)
    # print(Terminals)
    while True:
        s3.push()
        callId = -1
        for currentModel in Models:
            newVarTable = VarTable.copy()
            currentOuterCons = ReplacedCons.copy()
            for functionCallName in functionCallDic:
                returnValueVar, CurrentArguments = functionCallDic[functionCallName]
                InputValueVar = []
                OutputValueVar = []
                callId += 1
                ValueTypeNumber = {'Bool': len(Terminals['Bool']), 'Int': len(Terminals['Int'])}
                for i in range(len(Operators)):
                    operator = Operators[i]
                    outputType = operator[1]
                    outputValueVar = declareVar(outputType,
                                                getId(outputType + str(callId) + "-", ValueTypeNumber[outputType]),
                                                newVarTable)
                    OutputValueVar.append(outputValueVar)
                    ValueTypeNumber[outputType] += 1
                    currentInputValue = []
                    operatorTypeVar = OperatorTypeVar[i]
                    InputValueVarTable = []
                    for arg in operator[2:]:
                        if type(arg) == list:
                            inputType = arg[0]
                            inputValueVar = declareVar(inputType,
                                                       getId(inputType + str(callId) + "-", ValueTypeNumber[inputType]),
                                                       newVarTable)
                            InputValueVarTable.append(inputValueVar)
                            ValueTypeNumber[inputType] += 1
                            currentInputValue.append(inputValueVar)
                    # print(currentInputValue)
                    InputValueVar.append(currentInputValue)
                    for typeId in range(len(operator[0])):
                        currentCons = [operator[0][typeId]]
                        inputValueVarId = -1
                        for arg in operator[2:]:
                            if type(arg) == list:
                                inputValueVarId += 1
                                currentCons.append(str(InputValueVarTable[inputValueVarId]))
                            else:
                                currentCons.append(arg)
                        currentCons = ["=", str(outputValueVar), currentCons]
                        currentCons = ["=>", ["=", str(typeId), str(operatorTypeVar)], currentCons]
                        spec = '(assert %s)' % (translator.toString(currentCons))
                        spec = parse_smt2_string(spec, decls=dict(newVarTable))
                        # print(spec[0])
                        s3.add(spec[0])
                # print "CurrentArg: ", CurrentArguments
                # print ArgumentDict
                # print(InputValueVar)
                for i in range(len(Operators)):
                    for j in range(len(InputVar[i])):
                        inputVar = InputVar[i][j]
                        inputValue = InputValueVar[i][j]
                        for k in range(len(Operators)):
                            if i == k: continue
                            outputVar = OutputVar[k]
                            outputValue = OutputValueVar[k]
                            outputType = Operators[k][1]
                            if outputType in str(inputVar):
                                s3.add(Implies(outputVar == inputVar, outputValue == inputValue))
                        if "Bool" in str(inputVar):
                            currentType = "Bool"
                        else:
                            currentType = "Int"
                        for k in range(len(Terminals[currentType])):
                            terminal = Terminals[currentType][k]
                            if terminal in ArgumentDict:
                                argId = ArgumentDict[terminal]
                                currentCons = ["=>", ["=", str(inputVar), str(k)],
                                               ["=", CurrentArguments[argId], str(inputValue)]]
                            else:
                                currentCons = ["=>", ["=", str(inputVar), str(k)], ["=", terminal, str(inputValue)]]
                            currentCons = '(assert %s)' % (translator.toString(currentCons))
                            currentCons = parse_smt2_string(currentCons, decls=dict(newVarTable))
                            currentCons = currentModel.eval(currentCons[0])
                            s3.add(currentCons)
                newReturnValueVar = declareVar(ReturnType, getId("returnValueVar", callId), newVarTable)
                currentOuterCons = replaceCons(currentOuterCons, str(returnValueVar), str(newReturnValueVar))
                for k in range(len(Operators)):
                    outputVar = OutputVar[k]
                    outputValue = OutputValueVar[k]
                    outputType = Operators[k][1]
                    if outputType == ReturnType:
                        s3.add(Implies(resultVar == outputVar, newReturnValueVar == outputValue))
            spec = "\n".join(list(map(lambda x: "(assert %s)" % translator.toString(x[1:]), currentOuterCons)))
            spec = parse_smt2_string(spec, decls=newVarTable)
            #print(spec)
            spec = list(map(lambda x: currentModel.eval(x), spec))
            #print(spec)
            s3.add(spec)
        #print "start"
        #print(s3)
        resS3 = s3.check()
        # print(s3.unsat_core())
        # print(resS3)
        # print "end"
        # print(resS3)
        if resS3 == unsat:
            return None
        currentCodeModel = s3.model()
        s3.pop()
        OutputTable = {}
        for i in range(len(Operators)):
            outputId = currentCodeModel[OutputVar[i]].as_long()
            OutputTable[outputId] = i
        '''print("Now")
        for i in range(len(Operators)):
            print("")
            print(Operators[i])
            print(currentCodeModel[OutputVar[i]])
            print(map(lambda x: currentCodeModel[x], InputVar[i]))'''
        resultId = currentCodeModel[resultVar].as_long()
        # print(currentCodeModel)
        if resultId < len(Terminals[ReturnType]):
            resultCode = Terminals[ReturnType][resultId]
        else:
            resultCode = getCode(OutputTable[resultId], currentCodeModel, Operators, InputVar,
                                 OutputTable, Terminals, OperatorTypeVar)

        #print translator.toString(resultCode)

        s2.push()
        FuncDefineStr = '(define-fun'
        for i in range(1, 4):
            currentStr = translator.toString(SynFunExpr[i])
            if i == 2 and len(SynFunExpr[i]) == 1:
                currentStr = "(%s)"%(currentStr)
            FuncDefineStr += " " + currentStr
        FuncDefineStr += ")"
        #print FuncDefineStr
        fullResultCode = FuncDefineStr[:-1] + ' ' + translator.toString(resultCode) + FuncDefineStr[-1]
        spec_smt2=[fullResultCode]
        for constraint in Constraints:
            spec_smt2.append('(assert %s)'%(translator.toString(constraint[1:])))
        spec_smt2='\n'.join(spec_smt2)
        spec = parse_smt2_string(spec_smt2, decls=dict(VarTable))
        # print "End"
        s2.add(Not(And(spec)))

        while True:
            s2.push()
            s2.add(And(inputQualityCons))
            resS2 = s2.check()
            if resS2 == unsat:
                if len(inputQualityCons) == 0:
                    return fullResultCode
                else:
                    s2.pop()
                    inputQualityCons = inputQualityCons[:-1]
                    continue
            newInput = s2.model()
            s2.pop()
            break

        s2.pop()

        s1.push()
        for var in inputVarTable:
            newInputValue = newInput[inputVarTable[var]]
            if newInputValue is not None:
                s1.add(inputVarTable[var] == newInputValue)
        s1.check()
        newFullInput = s1.model()
        s1.pop()
        #print(newFullInput)
        #print(fullResultCode)
        #input()
        Models.append(newFullInput)
    return None


def checkOccur(Exp, term):
    # if term == '+' or term == '-': return False
    return True

def simplifyOperator(Operators):
    simpleOperators = []
    # print(Operators)
    for operatorType in Operators:
        isBool = True
        isInt = True
        # print(operatorType)
        for arg in operatorType[1:]:
            if arg != 'Bool' and arg != ['Bool']:
                isBool = False
            if arg != 'Int' and arg != ['Int']:
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
        if not isInt:
            simpleOperators.append([resultOperator] + operatorType[1:])
    return simpleOperators


if __name__ == '__main__':
    benchmarkFile = open(sys.argv[1])
    bm = stripComments(benchmarkFile)
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

    _, _, _, Constraints = translator.ReadQuery(bmExpr)

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
                if not checkOccur(bmExpr, NT[0]):
                    continue
                operatorStr = str([NonTerm[1], operatorArgs])
                if operatorStr in operatorTable:
                    operatorLoc = operatorTable[operatorStr]
                    Operators[operatorLoc][0].append(NT[0])
                else:
                    operator = [[NT[0]], NonTerm[1]]
                    operator.extend(operatorArgs)
                    operatorTable[operatorStr] = len(Operators)
                    Operators.append(operator)
    Operators = simplifyOperator(Operators)
    #print(Operators)

    times = 1
    #pprint.pprint(SynFunExpr)
    while True:
        print("CurrentT", times)
        result = trySolve(Terminals, Operators * times, ReturnType, bmExpr)
        if result is None:
            times += 1
            continue
        else:
            print(result)
            break