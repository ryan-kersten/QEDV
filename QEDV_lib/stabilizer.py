class Stabilizer:

    def __init__(self, qubits):
        """

        :param qubits: Set of ints, with the ints representing the qubits in the stabilizer
        """
        if not isinstance(qubits, set):
            raise TypeError("'qubits' be a set.")

        if not all(isinstance(el, (int, float)) for el in qubits):
            raise ValueError("All elements must be numbers.")

        self.qubits = frozenset(qubits)

        """
        Return a set of ints, representing the qubits in the stabilizer
        """
    def getQubits(self):
        return set(self.qubits)

    def __eq__(self, other):
        if not isinstance(other, Stabilizer):
            return NotImplemented
        return self.qubits == other.qubits

    def __hash__(self):
        return hash(self.qubits)