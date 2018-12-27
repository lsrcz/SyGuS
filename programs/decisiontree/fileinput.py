import sexp
import translator
from semantics import Func, exprFromList
from semanticschecker import SemChecker


def stripComments(bmFile):
    noComments = '('
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + ')'

def readin(filename):
    benchmarkFile = open(filename)
    bm = stripComments(benchmarkFile)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0]
    return bmExpr

def getZ3checker(bmExpr):
    return translator.ReadQuery(bmExpr)

def getProductions(bmExpr):
    SynFunExpr = []
    StartSym = 'My-Start-Symbol'
    StartBoolSym = 'My-Bool-Start-Symbol'
    for expr in bmExpr:
        if len(expr) == 0:
            continue
        elif expr[0] == 'synth-fun':
            SynFunExpr = expr

    productions = {StartSym: [], StartBoolSym: []}
    Type = {StartSym: SynFunExpr[3], StartBoolSym: 'Bool'}

    for NonTerm in SynFunExpr[4]:  # SynFunExpr[4] is the production rules
        NTName = NonTerm[0]
        NTType = NonTerm[1]
        if NTType == Type[StartSym]:
            productions[StartSym].append(NTName)
        if NTType == Type[StartBoolSym]:
            productions[StartBoolSym].append(NTName)
        Type[NTName] = NTType
        # Productions[NTName] = NonTerm[2]
        productions[NTName] = []
        for NT in NonTerm[2]:
            if type(NT) == tuple:
                productions[NTName].append([NT[0], NT[
                    1]])  # deal with ('Int',0). You can also utilize type information, but you will suffer from these tuples.
            else:
                productions[NTName].append(NT)
    # eliminateProductions(productions)

    arglist = []
    typelist = []
    for p in SynFunExpr[2]:
        arglist.append(p[0])
        typelist.append(p[1])
    functionProto = Func(SynFunExpr[1], arglist, typelist, SynFunExpr[3])
    return productions, functionProto

def getSemChecker(bmExpr, functionProto):
    inputlist = []
    inputtylist = []
    constraintlist = []
    for expr in bmExpr:
        if len(expr) == 0:
            continue
        elif expr[0] == 'declare-var':
            inputlist.append(expr[1])
            inputtylist.append(expr[2])
        elif expr[0] == 'constraint':
            if isinstance(expr[1], list):
                constraintlist.append(exprFromList(expr[1], {functionProto.name: functionProto}))
            else:
                constraintlist.append(exprFromList(expr[1:], {functionProto.name: functionProto}))
    return SemChecker(functionProto, constraintlist, inputlist, inputtylist)

def eliminateProductions(productions):
    # TODO: Not implemented well
    lt = False
    gt = False
    le = False
    ge = False
    for k in productions:
        for m in productions[k]:
            if isinstance(m, list) and m[0] == '<=':
                if ge == True:
                    productions[k].remove(m)
                else:
                    le = True
            if isinstance(m, list) and m[0] == '>=':
                if le == True:
                    productions[k].remove(m)
                else:
                    ge = True
            if isinstance(m, list) and m[0] == '<':
                if gt == True:
                    productions[k].remove(m)
                else:
                    lt = True
            if isinstance(m, list) and m[0] == '>':
                if lt == True:
                    productions[k].remove(m)
                else:
                    gt = True
            # dangerous
            if isinstance(m, list) and m[0] == 'not':
                productions[k].remove(m)
            if isinstance(m, list) and m[0] == 'Int':
                productions[k].remove(m)
    return productions