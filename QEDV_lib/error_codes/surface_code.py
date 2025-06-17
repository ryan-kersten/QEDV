import random

import stim

from QEDV_lib import ErrorCode, QuantumError


class SurfaceCode(ErrorCode):
    @staticmethod
    def _stabalizersFromSurface(n):
        output = set()
        for row in range(n + 1):
            parity = row % 2
            stabalize = ((n - parity) // 2)
            for i in range(stabalize):
                temp = set()
                rowOffset = max(0, (row - 1) * n)
                rowOffset = min((n - 1) * n, rowOffset)
                temp.add(i * 2 + parity + rowOffset)
                temp.add(i * 2 + parity + 1 + rowOffset)
                if (row > 0 and row < n):
                    temp.add(i * 2 + parity + n + rowOffset)
                    temp.add(i * 2 + parity + n + 1 + rowOffset)
                output.add(temp)
        return output

    def __init__(self, distance):
        self.stabilizers = self._stabalizersFromSurface(distance)
        self.qubits = distance**2

    def randomError(self,prob):
        randomError = set()
        for qubit in range(0,self.qubits):
            if random.random() < prob:
                randomError.add(qubit)
        return QuantumError(randomError)


    def STIMrandomError(self):
        surface_code_circuit = stim.Circuit.generated(
            "surface_code:rotated_memory_x",
            rounds=9,
            distance=3,
            after_clifford_depolarization=0.001,
            after_reset_flip_probability=0.001,
            before_measure_flip_probability=0.001,
            before_round_data_depolarization=0.001)
