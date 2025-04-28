import random

import numpy as np
import stim

from QEDV_lib import ErrorCode, Stabilizer, QuantumError


class SurfaceCodeStim(ErrorCode):
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
                output.add(Stabilizer(temp))
        return output

    @staticmethod
    def _stabalizersFromSurfaceInternal(n):
        output = list()
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
                output.append(Stabilizer(temp))
        return output

    def __init__(self, distance):
        self.stabilizers = self._stabalizersFromSurface(distance)
        self.dist = distance
        self.qubits = distance**2
        self.surface_code_circuit = stim.Circuit.generated(
            "surface_code:rotated_memory_x",
            rounds= distance*3,
            distance=distance,
            after_clifford_depolarization=0.001,
            after_reset_flip_probability=0.001,
            before_measure_flip_probability=0.001,
            before_round_data_depolarization=0.001)
        self.sampler = self.surface_code_circuit.compile_detector_sampler()
        self.numStab = len(self.stabilizers)
        self.curShot = 0
        self.curRound = 0
        self.stab, self.data = self.sampler.sample(self.dist**2,separate_observables = True)


    def randomError(self,prob):
        randomError = set()
        for qubit in range(0,self.qubits):
            if random.random() < prob:
                randomError.add(qubit)
        return QuantumError(randomError)


    def STIMrandomError(self):
        qubits = set()
        for index in range(self.dist):
            if self.data[index]:
                qubits.add(index)
        return QuantumError(qubits)




