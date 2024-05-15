import time
from incidence import *
from matplotlib import pyplot as plt
import pandas as pd
import numpy as np
import matplotlib.colors as mcolors
from matplotlib.ticker import FuncFormatter

# Generate concept lattice from incidence table and
# generate extensional and intensional wu-palmer scores for nodes in the concept lattice
def main1():
    start_time = time.time()
    I = csv_to_I('restaurants_fca.csv', incidence_symbols=['x'], sep=';')
    I.episteme.specification.refl_reduction().trans_reduction().to_graphml('rest_fca1.graphml')
    I.episteme.concepts_to_graphml('rest_fca2.graphml')

    lattice = I.episteme.specification
    lattice.assign_depths()
    lattice.assign_heights()

    #Extensional Wu-Palmer distances
    concepts = dict()

    # Get levels of atoms
    for node in lattice.nodes:
        # print(node.id, ' \t', node.lvl, '\t', node.A)
        for ext_elem in node.A:
            if ext_elem in concepts:
                if node.lvl > concepts[ext_elem].lvl:
                    concepts[ext_elem] = node
            else:
                concepts[ext_elem] = node

    headers = ['c1', 'c2', 'c1_depth', 'c2_depth', 'lcs_depth', 'wupalmer']
    results = [headers]
    crosstable_ext = []
    for concept1 in concepts.items():
        crosstable_row = [concept1[0]]
        for concept2 in concepts.items():
            lcs = lattice.join(concept1[1], concept2[1])
            wp = 2 * (lcs.lvl / (concept1[1].lvl + concept2[1].lvl))
            results.append([concept1[0], concept2[0], concept1[1].lvl, concept2[1].lvl, lcs.lvl, wp])
            crosstable_row.append(wp)
        crosstable_ext.append(crosstable_row)

    crosstable_ext.insert(0, [row[0] for row in crosstable_ext[1:]])
    for row in crosstable_ext:
        print(row)

    with open('rest_wupalmer_results1.csv', 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerows(results)

    with open('rest_wupalmer_crosstable1.csv', 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerows(crosstable_ext)

    #Intensional Wu-Palmer distances
    concepts = dict()

    # Get heights of atoms
    for node in lattice.nodes:
        # print(node.id, ' \t', node.lvl, '\t', node.A)
        for int_elem in node.B:
            if int_elem in concepts:
                if node.height > concepts[int_elem].height:
                    concepts[int_elem] = node
            else:
                concepts[int_elem] = node

    headers = ['c1', 'c2', 'c1_height', 'c2_height', 'lcs_height', 'wupalmer']
    results = [headers]
    crosstable_int = []

    for concept1 in concepts.items():
        crosstable_row = [concept1[0]]
        for concept2 in concepts.items():
            lcs = lattice.meet(concept1[1], concept2[1])
            wp = 2 * (lcs.height / (concept1[1].height + concept2[1].height))
            results.append([concept1[0], concept2[0], concept1[1].height, concept2[1].height, lcs.height, wp])
            crosstable_row.append(wp)
        crosstable_int.append(crosstable_row)

    crosstable_int.insert(0, [row[0] for row in crosstable_int])

    with open('rest_wupalmer_results2.csv', 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerows(results)

    with open('rest_wupalmer_crosstable2.csv', 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerows(crosstable_int)

    print("--- %s seconds ---" % (time.time() - start_time))


def main2():
    df = pd.read_csv('both_crosstable.csv', index_col=0, encoding="ISO-8859-1", sep=';')
    df = df.transpose()

    # Create a custom colormap ranging from reds to blues
    reds = plt.cm.Blues(np.linspace(0, 1, 128))
    blues = plt.cm.Reds(np.linspace(0, 1, 128))[::-1]
    colors = np.vstack((blues, reds))
    cmap = mcolors.ListedColormap(colors)

    # Create mask for the diagional
    mask = df.values == 1

    plt.figure(figsize=(8, 6))
    plt.imshow(df, cmap=cmap, interpolation='nearest', vmin=-1, vmax=1)

    # Define the formatter function to remove the '-' from negative numbers
    def custom_formatter(x, pos):
        if x < 0:
            return str(x)[1:]
        else:
            return str(x)

    # create dummy invisible image
    # (use the colormap you want to have on the colorbar)
    img = plt.imshow(np.array([[0, 1]]), cmap="Blues")
    img.set_visible(False)

    plt.colorbar(label='Intensional Wu-Palmer Similarity Scores', shrink=0.825)

    # create dummy invisible image
    # (use the colormap you want to have on the colorbar)
    img = plt.imshow(np.array([[0, 1]]), cmap="Reds")
    img.set_visible(False)

    plt.colorbar(label='Extensional Wu-Palmer Similarity Scores', cmap='Reds', shrink=0.825)

    colors = [(0, 0, 0, 0), (0, 0, 0)]  # transparent and black
    cmap = mcolors.ListedColormap(colors)

    plt.imshow(mask, cmap=cmap, interpolation='nearest', alpha=1, vmin=0, vmax=1)

    # Set ticks and labels
    plt.xticks(np.arange(len(df.columns)), df.columns)
    plt.yticks(np.arange(len(df.index)), df.index)

    # Rotate the tick labels and set alignment
    plt.xticks(rotation=45, ha='right')
    plt.yticks(rotation=0, ha='right')

    plt.tight_layout()
    plt.savefig('both_sim.png')


main1()
main2()
