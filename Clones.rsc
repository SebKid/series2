module Clones

import lang::java::m3::Core;
import lang::java::m3::AST;
import lang::java::jdt::m3::Core;
import lang::java::jdt::m3::AST;

import IO;
import List;
import Set;
import Map;
import DateTime;
import util::Math;

import Normalization;
import Project;
import Runner;

public M3 project;
public set[Declaration] ast;

// Minimum number of sub nodes an AST node must have in order to be eligible
// for the clone detection algorithm
public int massThreshold = 7;

// Similarity values for which pairs of sub trees are eligible for the clone
// detection algorithm. Each type of clone has a different value
public map[int, real] similarityThreshold = (1: 1.0, 2: 1.0, 3: 0.5);

// Similar sub trees are put in the same bucket for easier comparison in the next steps
public map[node, list[node]] buckets = ();
// Store the associated mass for each sub tree. We need this in order to iterate
// over buckets in ascending order of their sub tree mass
public rel[node, int] bucketMasses = {};
	
// List holding pairs of clones
public list[tuple[loc, loc]] clones = [];

public list[tuple[loc, loc]] detectClones(int cloneType, M3 projectFile, set[Declaration] astList) {
	project = projectFile;
	ast = astList;
	
	println("Analyzing project for clones of type <cloneType>");
	
	println("	Partitioning AST subtrees to buckets...");
	visit(ast) {
		case node x: {
			nodeMass = calculateNodeMass(x);
			if (nodeMass >= massThreshold) {
				if (cloneType in [2, 3]) {
					x = normalize(x);
				}
				if (buckets[x]?) {
					buckets[x] += x;
				} else {
					buckets[x] = [x];
				}
				bucketMasses += <x, nodeMass>;
			}
		}
	}

	println("	Sorting buckets by their subtree\'s node mass...");
	// Have a sorted list of buckets based on their sub tree mass
	lrel[node, int] sortedBucketMasses = sort(bucketMasses, bool(tuple[node, int] a, tuple[node, int] b) { return a[1] < b[1]; });
	
	println("	Comparing AST subtrees from each bucket...");
	// Iterate over all sorted buckets and compare each bucket's subtrees for similarity
	for (<subTree, _> <- sortedBucketMasses) {
		if (size(buckets[subTree]) < 2) continue;

		for (<x, y> <- combinations(buckets[subTree])) {
			subtreeSimilarity = calculateSubtreeSimilarity(x, y);

			if (subtreeSimilarity >= similarityThreshold[cloneType]) {
				removeAlreadyAddedSubClones(x);
				removeAlreadyAddedSubClones(y);
				addClonePair(x, y);
			}
		}
	}	
	return clones;
}

public loc getLocationOfNode(node subTree) {
	loc location = currentProject;

	if (Declaration d := subTree) {
		if (d.src?) {
			location = d.src;
		}
	} else if (Expression e := subTree) {
		if (e.src?) {
			location = e.src;
		}
	} else if (Statement s := subTree) {
		if (s.src?) {
			location = s.src;
		}
	}

	return location;
}

// Determine the number of nodes present in AST subtree with root x
private int calculateNodeMass(node x) {
	int mass = 0;
	visit(x) {
		case node _: mass += 1;
	}
	return mass;
}

// Determine the similarity between two AST subtrees
private real calculateSubtreeSimilarity(node x, node y) {
	list[node] xNodes = [];
	list[node] yNodes = [];

	visit(x) {
		case node n: xNodes += n;
	}
	visit(y) {
		case node n: yNodes += n;
	}

	s = size(xNodes & yNodes);
	l = size(xNodes - yNodes);
	r = size(yNodes - xNodes);
	
	return (2.0 * s) / (2 * s + l + r);
}
// Generate all combinations of two nodes from given input list
public lrel[node, node] combinations(list[node] nodes) {
	return [<nodes[i], nodes[j]> | i <- [0..(size(nodes) - 1)], j <- [(i+1)..(size(nodes))]];
}
// Remove sub clones of x that were already added to the clones list. Since we only care for clones,
// we are not interested in keeping sub clones of them also
private void removeAlreadyAddedSubClones(node x) {
	visit (x) {
		case node n: {
			nodeLocation = getLocationOfNode(n);
			for (<c1, c2> <- clones) {
				if (c1 == nodeLocation || c2 == nodeLocation) {
					clones = delete(clones, indexOf(clones, <c1, c2>));
				}
			}
		}
	}
}
private void addClonePair(node x, node y) {
	// TODO: if statement should be removed after fixing how the location is gotten for a node
	if (getLocationOfNode(x) != currentProject && getLocationOfNode(y) != currentProject) {
		clones += <getLocationOfNode(x), getLocationOfNode(y)>;
	}
}
public int countDuplicateLines() {
	count = 0;
	for (<c, _> <- clones) {
		count += numberOfLines(c) * 2;
	}
	return count;
}