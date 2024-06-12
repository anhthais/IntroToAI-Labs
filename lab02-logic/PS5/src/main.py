from typing import List, Tuple
from pathlib import Path


# ==============================CLASSES==============================
class Literal:
    """
    A literal is a symbol that may be negated or unnegated
    """

    def __init__(self, symbol: str, negated: bool):
        self.symbol = symbol
        self.negated = negated

    def __repr__(self):
        return "-" + self.symbol if self.negated else self.symbol

    # Override ==, hash, < to make Literal objects become hashable
    # and be able to used in set, sorted...
    def __eq__(self, other):
        return self.symbol == other.symbol and self.negated == other.negated

    def __hash__(self):
        representation = "-" + self.symbol if self.negated else self.symbol
        return hash(representation)

    def __lt__(self, other):
        """
        - Sort literals
        - Eg: A < -A, A < B, -A < B
        """
        if self.symbol != other.symbol:
            return self.symbol < other.symbol
        return self.negated < other.negated

    def negate(self):
        self.negated = not self.negated

    def is_complement(self, other) -> bool:
        return self.negated != other.negated and self.symbol == other.symbol

    @staticmethod
    def parse(literal_str):
        """
        - Parse a string to a literal
        - Eg: '-A' -> Literal('A', True)
        """
        if literal_str[0] == "-":
            return Literal(literal_str[1], True)
        else:
            return Literal(literal_str[0], False)


class Clause:
    """
    A clause is a disjunction of literals
    """

    def __init__(self):
        self.literals = []

    def __repr__(self):
        if len(self.literals) != 0:
            return " OR ".join(str(literal) for literal in self.literals)
        else:
            return "{}"

    # Override ==, hash, < to make Clause objects become hashable
    # and be able to used in set, sorted...
    def __eq__(self, other):
        return set(self.literals) == set(other.literals)

    def __hash__(self):
        return hash(tuple(self.literals))

    def __lt__(self, other):
        """
        - Sort clauses
        - Priority: length of literals -> literals
        - Eg:
            - 'A OR B' < 'A OR B OR C'
            - 'A OR B' < 'A OR C'
        """
        if len(self.literals) != len(other.literals):
            return len(self.literals) < len(other.literals)
        for i in range(len(self.literals)):
            if self.literals[i] != other.literals[i]:
                return self.literals[i] < other.literals[i]
        return False

    def is_empty(self):
        return len(self.literals) == 0

    def add_literal(self, literal: Literal):
        self.literals.append(literal)

    def refactor(self):
        """
        Remove duplicates and sort
        """
        self.literals = sorted(set(self.literals))

    def is_always_true(self) -> bool:
        """
        - Check if a clause is always true, the clause was sorted
        - Eg: 'A OR -A OR B' = 'TRUE OR A' = 'TRUE'
        """
        for i in range(len(self.literals) - 1):
            if self.literals[i].is_complement(self.literals[i + 1]):
                return True
        return False

    def merge(self, other: "Clause") -> "Clause":
        """
        - Merge 2 clauses
        - Eg: 'A OR B', '-A OR C' => 'B OR C'
        """
        new_clause = Clause()
        new_clause.literals = self.literals + other.literals
        new_clause.refactor()
        return new_clause

    def clone_without(self, literal: Literal) -> "Clause":
        """
        - Clone clause without a literal
        - Eg: 'A OR B OR C' without 'A' => 'B OR C'
        """
        new_clause = Clause()
        for l in self.literals:
            if l != literal:
                new_clause.add_literal(l)
        new_clause.refactor()
        return new_clause

    @staticmethod
    def parse(clause_str):
        """
        - Parse a string to a clause
        - Eg: 'A OR B OR -C' -> Clause([Literal('A', False), Literal('B', False), Literal('C', True)])
        """
        clause = Clause()
        for literal_str in clause_str.split(" OR "):
            literal_str = literal_str.strip()
            clause.add_literal(Literal.parse(literal_str))
        clause.refactor()
        return clause

    def pl_resolve(self, other: "Clause"):
        """
        - Return the set of all possible resolvents and a boolean value to check if there is an empty clause
        - Eg: 'A OR B OR C', '-A OR D OR -C'
            - 'A' is complement of '-A' => resolvent = 'B OR C OR -C OR D' = TRUE => discard
            - 'C' is complement of '-C' => resolvent = 'A OR B OR -B OR D' = TRUE => discard
            - Result: resolvents = {}, has_empty_clause = FALSE
        """
        resolvents = set()
        has_empty_clause = False

        for literal1 in self.literals:
            for literal2 in other.literals:
                if literal1.is_complement(literal2):
                    clause1 = self.clone_without(literal1)
                    clause2 = other.clone_without(literal2)
                    resolvent = clause1.merge(clause2)

                    if resolvent.is_always_true():
                        continue
                    if resolvent.is_empty():
                        has_empty_clause = True
                    resolvents.add(resolvent)

        return resolvents, has_empty_clause


class KnowledgeBase:
    def __init__(self):
        self.clauses = []

    def add_clause(self, clause: Clause):
        self.clauses.append(clause)

    @staticmethod
    def parse(clauses: List[str]) -> "KnowledgeBase":
        kb = KnowledgeBase()
        for clause_str in clauses:
            clause = Clause.parse(clause_str)
            clause.refactor()
            kb.add_clause(clause)
        return kb

    def pl_resolution(self, alpha: str) -> Tuple[bool, List[List[str]]]:
        """
        - PL resolution algorithm
        - Return a boolean value to check if alpha is entailed by KB and a list of new clauses
        - alpha: a string represents a clause. We need to negate it before adding to KB, i.e. negate each literal and convert to CNF clause
            - Eg: 'A OR B' => '-A AND -B'
        """
        # 1. Create 'clauses' is a set of clauses of KB and -alpha
        clauses = self.clauses.copy()
        alpha_literals = alpha.split(" OR ")
        for literal_str in alpha_literals:
            literal_str = literal_str.strip()
            literal = Literal.parse(literal_str)
            literal.negate()
            clause = Clause()
            clause.add_literal(literal)
            if clause not in clauses:  # Remove duplicate clauses
                clauses.append(clause)

        # 2. Loop
        clauses = set(clauses)
        output = []  # output is a list of new clauses
        is_unsatisfiable = False

        while True:
            # 2.1. Loop through all pairs of clauses and resolve them
            new_clauses = set()
            for clause1 in clauses:
                for clause2 in clauses:
                    resolvents, has_empty_clause = clause1.pl_resolve(clause2)
                    new_clauses.update(resolvents)
                    if has_empty_clause:
                        is_unsatisfiable = True
                        break

            # Create a set of new clauses that are not in the 'clauses' set to the 'output' list
            output.append(new_clauses.difference(clauses))

            # 2.2. Check if there is an empty clause or no new clause
            if is_unsatisfiable:
                return True, output

            # 2.3. Check if new_clauses is a subset of clauses
            if new_clauses.issubset(clauses):
                return False, output

            # 2.4. Update clauses
            clauses.update(new_clauses)


# ==============================I/O==============================
def read_input(path: Path) -> Tuple[str, List[str]]:
    with path.open() as file:
        alpha = file.readline().strip()
        num_clauses = int(file.readline())
        clauses = [file.readline().strip() for _ in range(num_clauses)]
    return alpha, clauses


def write_output(path: Path, entail: bool, output_clauses: List[List[str]]):
    with path.open(mode="w") as file:
        for clauses in output_clauses:
            file.write(f"{len(clauses)}\n")
            for clause in clauses:
                file.write(f"{clause}\n")
        if entail == True:
            file.write("YES")
        else:
            file.write("NO")


# ==============================MAIN==============================
if __name__ == "__main__":
    input_folder = Path("./input")
    output_folder = Path("./output")
    if not output_folder.exists():
        output_folder.mkdir()

    for input_file in input_folder.glob("*.txt"):
        src = input_file.name
        des = output_folder.joinpath(src.replace("input", "output"))

        alpha, clauses = read_input(input_file)
        KB = KnowledgeBase.parse(clauses)
        entail, output_clauses = KB.pl_resolution(alpha)
        write_output(des, entail, output_clauses)
