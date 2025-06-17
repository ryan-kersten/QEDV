import time

from QEDV_lib import ErrorCode
from QEDV_lib import Stabilizer
import numpy as np
from QEDV_lib.error_code import *
from QEDV_lib.error_codes import SurfaceCode
from QEDV_lib.error_codes.bicycle_code import BicycleCode
from QEDV_lib.error_codes.surface_codeSTIM import SurfaceCodeStim
from QEDV_lib.verifier import Verifier




def performanceProfilingBrute(data):
    bruteTime = 0
    elapsedBrute = 0

    for index, trial in enumerate(data["trials_test"].to_list()):
        dim = data["Dimension"].to_list()[index]
        start_time = time.perf_counter()
        code = SurfaceCode(dim)
        result = Verifier._BruteForcestabilizerCheck(code, trial)
        end_time = time.perf_counter()
        # print("ran iter", index)
        execution_time = end_time - start_time
        bruteTime += execution_time
        data["BruteTime"][index] = execution_time
        data["Brute"][index] = True



def perfomanceProfilingSurfaceCode(roundsPerDistance, Dimensions, probs, keepErrors = False, data= None):
    if data is None:
        data = {
            "Error Rate": [],
            "Dimension": [],
            "Solvable": [],
            "rlimit": [],
            "time": [],
            "Brute": [],
            "BruteTime": [],
            "trials_test": [],
            "trial_dim": []
        }
    import pymatching
    import itertools
    elapsedBrute = 0
    elapsedSolver = 0
    solverTime = 0
    bruteTime = 0
    flag = False


    for p_err in probs:
        for dim in Dimensions:
            print("RUNNING NEW DIMENSION", dim)
            code = BicycleCode(dim)
            # check = _checkMatrix(code.getStabilizers(), dim ** 2)
            for iter in range(0, roundsPerDistance):
                random_error = code.randomError(p_err)
                if keepErrors:
                    data["trials_test"].append(random_error)
                else:
                    data["trials_test"].append(None)
                start_time = time.perf_counter()
                result = Verifier.stabalizerCheck(code, random_error)
                end_time = time.perf_counter()
                execution_time = end_time - start_time
                solverTime += execution_time
                elapsedSolver += execution_time
                data["Error Rate"].append(p_err)
                data["Dimension"].append(dim)
                data["Solvable"].append(result[0])
                if result[1] is None:
                    data["rlimit"].append(0)
                else:
                    data["rlimit"].append(result[1].get_key_value('rlimit count'))
                data["time"].append(execution_time)
                data["Brute"].append(False)
                data["BruteTime"].append(0)
                data["trial_dim"].append(dim)
                if solverTime > 3600:
                    # print("BRUTE FORCE RAN OUT AT DIM", dim, "AT STEP", iter, "/", roundsPerDistance)
                    flag = False
                    break
                if elapsedSolver > 10 or elapsedBrute > 10:
                    # print("Brute Solver has taken:", bruteTime)
                    # print("SAT Solver has taken:", solverTime)
                    # print("CALCULATING DISTANCE", dim)
                    elapsedSolver = 0
                    elapsedBrute = 0
                ...
                # print("finished Iter,", iter, "/", roundsPerDistance)

            if flag:
                break
                # print("finished Iter,", iter, "/", roundsTORunEachDistance)
        print("RAN PROB", p_err)
    return data




if __name__ == "__main__":
    import seaborn as sns
    import sys
    import matplotlib.pyplot as plt
    import pandas as pd

    output_dir = sys.argv[1]

    start_time = time.time()
    timeout = 1000000000
    i = 0
    while time.time() - start_time < timeout:
        i += 1
        data = perfomanceProfilingSurfaceCode(50,[0,1], [.001,.01,.05,.1,.2,.35,.3,.25,.5],True)
        df = pd.DataFrame(data)
        name = output_dir + '/' + str(i) + "data.pkl"
        df.to_pickle(name)
        print("PICKLED")



