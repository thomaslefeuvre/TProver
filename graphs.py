
import csv
import math
import numpy as np
import matplotlib.mlab as mlab
import matplotlib.pyplot as plt


def create_dict(data):
    # creates a dictionary of data with running arguments as keys
    split = [[]]*(len(data)//275)

    j = 0
    for i in range(0,len(data), 275):
        split[j] = data[i:i+275]
        j += 1

    result = dict()

    for i in range(len(split)):
        result[split[i][0]] = split[i][1:]

    return result


def find(d, **arguments):
    # returns a list of lists matching arguments
    keys = list(d.keys())

    try:
        if arguments['init']:
            keys = filter(lambda x: "-init %d" % arguments['init'] in x, keys)
    except KeyError:
        pass

    try:
        if arguments['cnf']:
            keys = filter(lambda x: "-cnf %d" % arguments['cnf'] in x, keys)
    except KeyError:
        pass

    try:
        if arguments['pl']:
            keys = filter(lambda x: "-pl" in x, keys)
        else:
            keys = filter(lambda x: "-pl" not in x, keys)
    except KeyError:
        pass

    try:
        if arguments['iffs']:
            keys = filter(lambda x: "-iffs" in x, keys)
        else:
            keys = filter(lambda x: "-iffs" not in x, keys)
    except KeyError:
        pass

    try:
        if arguments['unit']:
            keys = filter(lambda x: "-unit" in x, keys)
        else:
            keys = filter(lambda x: "-unit" not in x, keys)
    except KeyError:
        pass

    try:
        if arguments['sub']:
            keys = filter(lambda x: "-sub" in x, keys)
        else:
            keys = filter(lambda x: "-sub" not in x, keys)
    except KeyError:
        pass

    result = []
    avgs = []
    for k in keys:
        result.append(d[k])
    for i in range(274):
        ith = []
        for x in result:
            ith.append(x[i])
        solved = [y for y in ith if y != 64]
        avg = 64
        if len(ith) - len(solved) < len(ith) / 2.0:
            avg = sum(solved) / float(len(solved))
        avgs.append(avg)
    return [avgs]

def find2(d, p):
    result = []
    result.append(d[p])
    return result


def plot(data, colour, linewidth=1):
    # plots data for lists in data, for given colour
    for i in range(len(data)):
        x = plt.hist([d for d in data[i] if d != 64], bins=bins, alpha=1, histtype='step', cumulative=True, color=colour, linewidth=linewidth)
    return x


if __name__ == '__main__':
    
    results = []
    with open('results/comparison.csv', 'rb') as f:
        reader = csv.reader(f)
        for row in reader:
            for cell in row:
                try:
                    results.append(float(cell.strip()))
                except ValueError:
                    results.append(cell)

    # code to run
    d = create_dict(results)
    
    # # gather data
    r1 = find2(d, 'TProver')
    r2 = find2(d, 'prover9')
    r3 = find2(d, 'vampire')
    # r1 = find(d, sub=True, pl=True, cnf=1, init=3, unit=True, iffs=True)
    # r1 = find(d, sub=True)
    # r2 = find(d, sub=False)
    # r2 = find(d, sub=False, pl=False)
    # r2 = find(d)
    # r3 = find(d, sub=False, cnf=1, pl=False, init=1, unit=False, iffs=False)
    # r3 = find(d, init=3)
    # plot setup
    from matplotlib.ticker import ScalarFormatter
    from matplotlib.ticker import FormatStrFormatter
    fig, ax = plt.subplots()
    bins = np.logspace(-8, 8, 10000, base=2.0)
    plt.xlim([2 ** -8,64])
    plt.ylim([0,300])

    plot(r3, 'g')
    plot(r2, 'b')
    plot(r1, 'r')
    # plot(r4, 'm')

    plt.plot((-20,64),(274,274), color='k')
    plt.gca().set_xscale("log", basex=10)
    ax.xaxis.set_major_formatter(FormatStrFormatter('%.2f'))
    # ax.get_xaxis().get_major_formatter().set_useOffset(False)
    # plt.set_major_formatter(ScalarFormatter())
    plt.xlabel("Time (s)")
    plt.ylabel("Cumulative problems solved")

    y = plt.plot((-1000,-1000),(0,0), color='r')
    x = plt.plot((-1000,-1000),(0,0), color='b')
    z = plt.plot((-1000,-1000),(0,0), color='g')
    # y = plt.plot((-1000,-1000),(0,0), color='m')

    plt.legend(['Total problems','TProver', 'Prover9', 'Vampire'], loc=4)

    # show graph
    plt.show()
