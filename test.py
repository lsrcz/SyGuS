#!/usr/bin/python  
import datetime
import os
import os.path
import platform
import signal
import subprocess
import time

import sexp
import translator

programdir = './programs/'
testroot = './tests/'
hiddentests = testroot + 'hidden_tests/'
opentests = testroot + 'open_tests/'


class TimeoutError(Exception):
    pass


def stripComments(bmFile):
    noComments = '('
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + ')'


def run_command(cmd, timeout=60):
    is_linux = platform.system() == 'Linux'

    p = subprocess.Popen(cmd, stderr=subprocess.STDOUT, stdout=subprocess.PIPE, shell=True,
                         preexec_fn=os.setsid if is_linux else None)
    t_beginning = datetime.datetime.now()
    seconds_passed = 0
    while True:
        timepassed = datetime.datetime.now() - t_beginning
        rtimepassed = timepassed.seconds + timepassed.microseconds / 1000000.0
        if p.poll() is not None:
            break
        if timeout and rtimepassed > timeout:
            if is_linux:
                os.killpg(p.pid, signal.SIGTERM)
            else:
                p.terminate()
            raise TimeoutError(cmd, timeout)
        time.sleep(0.01)
    return p.stdout.read(), rtimepassed


def bytesToStr(item):
    if isinstance(item, bytes):
        return str(item, encoding='utf-8')
    if isinstance(item, list):
        return list(map(bytesToStr, item))
    if isinstance(item, tuple):
        return tuple(map(bytesToStr, item))
    return item


def my_test(cmd, outputfile, testname, timeout=300):
    outputfile.write('\t%s:' % (testname))
    print(cmd)
    try:
        result, rtime = run_command(cmd, timeout)
    except TimeoutError:
        outputfile.write('timeout after %i \n' % (timeout))
    else:
        print(result)
        benchmarkFile = open(testname)
        bm = stripComments(benchmarkFile)
        bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0]  # Parse string to python list
        checker = translator.ReadQuery(bmExpr)
        try:
            checkresult = checker.check(str(result, encoding='utf-8'))
        except Exception as e:
            # outputfile.write('Wrong Answer: Invalid check result %s(%f)\n' %(result,rtime))
            outputfile.write('Invalid format(%f)\n' % (rtime))
        else:
            if (checkresult == None):
                outputfile.write('Passed(%f)\n' % (rtime))
            else:
                # outputfile.write('Wrong Answer: get %s(%f)\n' %(result,rtime))
                outputfile.write('Wrong Answer(%f)\n' % (rtime))


if __name__ == '__main__':
    timeout = 300
    testresultfile = 'testresult.txt'
    outfile = open(testresultfile, 'w')

    i = 0
    for studentname in os.listdir(programdir):
        if studentname != "jry2" and studentname != "combine" and studentname != "decisiontree": continue
        toexe = programdir + '\'' + studentname + '\'' + '/main.py '
        outfile.write(studentname + ': \n')
        # cmd = ('python3.5 ' if '3.5' in studentname else 'python ')
        cmd = 'python3 '
        i = i + 1
        print(i)
        # arg = opentests + 'three.sl'
        # my_test(cmd + toexe + arg, outfile, arg, timeout)
        for testgroup in [opentests]:
            for test in os.listdir(testgroup):
                if '.sl' not in test: continue
                arg = testgroup + test
                my_test(cmd + toexe + arg, outfile, arg, timeout)
