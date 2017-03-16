class Term:
    def __init__(self, init=[], symbol=None):
        if symbol is not None:
            self.symbolList = [symbol]
        else:
            self.symbolList = init

    def neg(self):
        self.symbolList = ["~", "("] + self.symbolList + [")"]

    def connect(self, term, op):
        self.symbolList = ["("] + self.symbolList
        self.symbolList += [op]
        self.symbolList += term
        self.symbolList += [")"]

    def printSentence(self):
        string = ""
        for symbol in self.symbolList:
            string += symbol+" "
        string.rstrip()
        print(string)

class Enumerator:
    defaultOps=["->", "/\\", "\\/"]
    defaultTermList=[Term(symbol="A"), Term(symbol="True"), Term(symbol="False")]
    def __init__(self, termList=defaultTermList, ops=defaultOps):
        self.termList=termList
        self.ops=ops

    def enumerate(self, depth=2):
        termPairList = self.CartesianProduct(self.termList)
        termList = self.termList
        n = 0
        while (True):
            newTermList = self.createNewTerm(termPairList)
            if (n == depth):
                break
            else:
                n += 1
            termPairList = self.createPairList(termList, newTermList)
            termList += newTermList
        termList += newTermList
        for term in termList:
            term.printSentence()
            

    def init(self):
        pass

    def CartesianProduct(self, termList):
        termPairList=[]
        for termA in termList:
            for termB in termList:
                termPairList.append((termA, termB))

        return termPairList

    def createNewTerm(self, termPairList):
        newTermList = []
        # connect with every op
        for termPair in termPairList:
            for op in self.ops:
                newTerm = Term(termPair[0].symbolList)
                newTerm.connect(termPair[1].symbolList, op)
                newTermList.append(newTerm)
        return newTermList

    def createPairList(self, termList, newTermList):
        termPairList = []
        for termA in termList:
            for termB in newTermList:
                termPairList.append((termA, termB))
                termPairList.append((termB, termA))
        termPairList += self.CartesianProduct(newTermList)
        return termPairList




newEnum = Enumerator()
newEnum.enumerate(depth = 2)
