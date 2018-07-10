from random import randrange, choice


class Child:
    def __init__(self):
        self.gender = choice(['boy', 'girl'])
        self.age = randrange(18)


from operator import attrgetter


def mr_jones():
    child_1 = Child()
    child_2 = Child()
    eldest = max(child_1, child_2, key=attrgetter('age'))
    assert eldest.gender == 'girl'
    return [child_1, child_2]


def mr_smith():
    child_1 = Child()
    child_2 = Child()
    assert child_1.gender == 'boy' or \
           child_2.gender == 'boy'
    return [child_1, child_2]


def expect(predicate, process, iterations=100):
    success, tot = 0, 0
    for _ in range(iterations):
        try:
            success += predicate(process())
            tot += 1
        except AssertionError:
            pass
    return success / tot


p_1 = expect(
    lambda children: all(child.gender == 'girl'
                         for child in children),
    mr_jones)
p_2 = expect(
    lambda children: all(child.gender == 'boy'
                         for child in children),
    mr_smith)
