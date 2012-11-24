#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
/*#include "bfs.h"*/

//#define MAX_NODES 1000
//#define INFINITY 100000

/*const int MAX_NODES = 1000;*/

struct node {
  int nNeighbours;
  int *neighbours;
  int distance;
};
/*typedef struct node node_t;*/

/*@
 
predicate integers(int *start, int count) =
  count <= 0 ? true : integer(start, _) &*& integers(start + 1, count - 1);

predicate node(struct node *no, int d, int *nb, int nNeighbours) =
  no != 0 &*&
  no->distance |-> d &*&
  no->neighbours |-> nb &*&
  no->nNeighbours |-> nNeighbours &*&
  integers(nb, nNeighbours)
  ;

inductive nodes = nodes_nil | nodes_cons(struct node *, nodes);

fixpoint int nodes_count(nodes values) {
  switch (values) {
    case nodes_nil: return 0;
    case nodes_cons(start, values0): return nodes_count(values0) + 1;
  }
}

predicate nodes_predicate(struct node *start, int count, nodes values) =
  count == 0 ?
  values == nodes_nil :
  node(start, _, _, _) &*&
  nodes_predicate(start + 1, count - 1, ?nodes0) &*&
  values == nodes_cons(start, nodes0);

lemma void nodes_append(struct node *start, struct node *new)
  requires nodes_predicate(start, ?count, ?values) &*&
           node(new, _, _, _) &*&
           new == start + count &*&
           count >= 0;
  ensures nodes_predicate(start, count + 1, ?values2);
{
  open nodes_predicate(start, count, values);
  if (count != 0) {
    nodes_append(start + 1, new);
    close nodes_predicate(start, count + 1, _);
  } else {
    close nodes_predicate(start + 1, 0, nodes_nil);
    close nodes_predicate(
      start + count, 1, nodes_cons(start + count, nodes_nil));
  }
}

//lemma void nodes_extract(struct node *start, int offset, int target_offset)
//  requires  nodes_predicate(start, ?count1, ?values1) &*&
//            nodes_predicate(start + count1, ?count2, ?values2) &*&
//            offset >= 0 &*&
//            offset <= count1 + count2 &*&
//            target_offset >= 0 &*&
//            target_offset <= count1 + count2 &*&
//            count1 >= 0 &*&
//            count2 >= 0 &*&
//            count1 + count2 > 0 &*&
//            offset <= target_offset &*&
//            offset + count2 >= target_offset;
//  ensures   nodes_predicate(start, offset, ?values3) &*&
//            node(start + offset, _, _, _) &*&
//            nodes_predicate(start + offset + 1,
//                            count1 + count2 - offset - 1,
//                            ?values4);
//{
//  if (offset < target_offset) {
//    open nodes_predicate(start + count1, count2, values2);
//    nodes_append(start, start + count1);
//    nodes_extract(start, offset + 1, target_offset);
//    
//  }
//}

  
@*/

void bfs(struct node *nodes, int nNodes)
  //@ requires nNodes > 0 &*& nodes_predicate(nodes, nNodes, ?values) &*& nNodes == nodes_count(values);
  //@ ensures nodes_predicate(nodes, nNodes, _);
{
  const int INFINITY = 100000;
  /// open nodes_predicate(nodes, nNodes, values);
  //@ close nodes_predicate(nodes, 0, nodes_nil);
  int i;
  for (i = 0; i != nNodes; i++)
    //@ invariant nodes_predicate(nodes, i, ?values1) &*&  nodes_predicate(nodes + i, nNodes - i, ?values2) &*&  i >= 0;
  {
    assert(i + 1 > 0);
    //@ open nodes_predicate(nodes + i, nNodes - i, values2);
    //@ open node(nodes + i, _, _, _);
    (nodes + i)->distance = INFINITY;
    //@ close node(nodes + i, INFINITY, _, _);
    //@ nodes_append(nodes, nodes + i);
  }
  //@open nodes_predicate(nodes + i, 0, _);
  assert(i == nNodes);
  int queue[1000];
  int begin = 0;
  int end = 1;
  queue[begin] = 0;
  struct node *node = nodes;
  //@ open nodes_predicate(nodes, nNodes, _);
  //@ open node(nodes, _, _, _);
  node->distance = 0;
  //@ close node(node, 0, _, _);
  //@ close nodes_predicate(nodes, nNodes, _);
}
    /// invariant node(nodes + i, _, _, _);

/*void bfs(node_t *nodes, int nNodes, int start)*/
/*{*/

  /*while(begin < end) {*/
    /*printf("Popped node %d from stack.\n", queue[begin]);*/
    /*node_t node = nodes[queue[begin++]-1];*/
    
    /*for (int j = 0; j < nNodes; j++) {*/
      /*if (node.neighbours[j]) {*/
        /*int neighbourId = node.neighbours[j];*/
        /*nodes[neighbourId-1].distance = node.distance + 1;*/
        /*queue[end++] = neighbourId;*/
      /*}*/
      /*else*/
        /*break;*/
    /*}*/
  /*}*/
/*}*/

// Input format:
// * Node numbering starts at 1.
// * On the 1st line: {#nodes} {#root-node} <- we might require this to be 1
// * On each of the following #nodes lines: {#children} {child_1} ... {child_n}
/*int main()*/
  /*//@ requires true;*/
  /*//@ ensures true;*/
/*{*/
  /*int nNodes, start;*/
  /*int **neighbours;*/

  /*[>scanf("%d %d\n", &nNodes, &start);<]*/
  /*nNodes = 4;*/
  /*start = 1;*/
  /*neighbours = calloc(nNodes, sizeof(int));*/
  /*if (neighbours == 0) {*/
    /*abort();*/
  /*}*/
  /*[>node_t nodes_data[1000];<]*/
  /*[>node_t *nodes = nodes_data;<]*/
  

  /*[>int size = 1000 * sizeof(int);<]*/
  /*[>int *neighbours;<]*/
  /*[>neighbours = malloc(size);<]*/

  /*[>node_t *node = nodes + 0;<]*/

  /*[>(nodes + 0)->neighbours = neighbours;<]*/
  /*[>(nodes + 0)->neighbours[0] = 2;<]*/
  /*[>nodes[0].neighbours[1] = 4;<]*/
  /*[>nodes[0].neighbours[2] = 0;<]*/
  /*[>nodes[1].neighbours[0] = 0;<]*/
  /*[>nodes[2].neighbours[0] = 0;<]*/
  /*[>nodes[3].neighbours[0] = 3;<]*/
  /*[>nodes[3].neighbours[1] = 0;<]*/
  
  /*[>for (int i = 0; i < nNodes; i++) {<]*/
    /*[>int nChildren;<]*/
    /*[>scanf("%d", &nChildren);<]*/
    /*[>int j = 0;<]*/
    /*[>for (; j < nChildren; j++) {<]*/
      /*[>scanf("%d", &(nodes[i].neighbours[j]));<]*/
    /*[>}<]*/
    /*[>// mark the end<]*/
    /*[>nodes[i].neighbours[j] = 0;<]*/
  /*[>}<]*/
  
  /*[>bfs(nodes, nNodes, start);<]*/
  /*[>for (int i = 0; i < nNodes; i++) {<]*/
    /*[>printf("distance(%d) = %d\n", i, nodes[i].distance);<]*/
  /*[>}<]*/

  /*free(neighbours);*/
  
  /*return 0;*/
/*}*/
