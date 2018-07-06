from random import randrange


def roll_die():
    return randrange(1, 7)

def expect(predicate, process, iterations):
    return sum(predicate(process())
               for _ in range(iterations)) / iterations


print(expect(lambda y: 5 == y, roll_die, 100))
