import multiprocessing
import jry2.main
import decisiontree.main
import sys

funcs = [jry2.main.main, decisiontree.main.main]
ids = ["jry2", "decisiontree"]

def main():
    manager = multiprocessing.Manager()
    return_dict = manager.dict()
    jobs = []
    for func in funcs:
        p = multiprocessing.Process(target=func, args=(return_dict,))
        jobs.append(p)
        p.start()
    
    found = False
    while True:
        for (p, s) in zip(jobs, ids):
            if not p.is_alive():
                if return_dict[s] != "invalid":
                    print(return_dict[s])
                    found = True
                    break
        if found:
            break

    for p in jobs:
        p.terminate()

if __name__ == '__main__':
    main()

