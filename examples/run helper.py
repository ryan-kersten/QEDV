import time

from QEDV_lib import ErrorCode
from QEDV_lib import Stabilizer
import numpy as np

from QEDV_lib.error_codes import SurfaceCode
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
        print("ran iter", index)
        execution_time = end_time - start_time
        bruteTime += execution_time
        data["BruteTime"][index] = execution_time
        data["Brute"][index] = True
        if elapsedSolver > 10 or elapsedBrute > 10:
            print("Brute Solver has taken:", bruteTime)
            print("CALCULATING DISTANCE", dim)
            elapsedSolver = 0
            elapsedBrute = 0



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
        for dim in range(Dimensions[0], Dimensions[1], 2):
            print("RUNNING NEW DIMENSION", dim)
            code = SurfaceCode(dim)
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
                data["rlimit"].append(result[1].get_key_value('rlimit count'))
                data["time"].append(execution_time)
                data["Brute"].append(False)
                data["BruteTime"].append(0)
                data["trial_dim"] = dim
                if solverTime > 3600:
                    print("BRUTE FORCE RAN OUT AT DIM", dim, "AT STEP", iter, "/", roundsPerDistance)
                    flag = False
                    break
                if elapsedSolver > 10 or elapsedBrute > 10:
                    print("Brute Solver has taken:", bruteTime)
                    print("SAT Solver has taken:", solverTime)
                    print("CALCULATING DISTANCE", dim)
                    elapsedSolver = 0
                    elapsedBrute = 0
                print("finished Iter,", iter, "/", roundsPerDistance)

            if flag:
                break
                # print("finished Iter,", iter, "/", roundsTORunEachDistance)
        print("RAN PROB", p_err)
    return data




if __name__ == "__main__":
    import seaborn as sns
    import matplotlib.pyplot as plt
    import pandas as pd

    print("HI")
    data = perfomanceProfilingSurfaceCode(10,[3,9], [.1,.2])
    dfRaw = pd.DataFrame(data)

    df = dfRaw[dfRaw["Brute"] == False]

    df_melted = df.melt(id_vars=["Dimension"], value_vars=["time", "BruteTime"],
                           var_name="Time Type", value_name="Time")
    # Create the bar plot
    sns.barplot(x="Dimension", y="Time", hue="Time Type", data=df_melted)
    plt.yscale('log')
    # Customize the plot (optional)
    plt.title("Comparison of Time and BruteTime by Dimension")
    plt.xlabel("Dimension")
    plt.ylabel("Time (Log Scale)")

    # Show the plot
    plt.show()
    print(df.memory_usage(deep=True).sum())
    df.to_pickle("data.pkl")



