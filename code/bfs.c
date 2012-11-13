#include <stdio.h>
#include <stdlib.h>

#define MAX_NODES 1000
#define INFINITY 100000


struct node {
  int neighbours[MAX_NODES];
  int distance;
};
typedef struct node node_t;

void bfs(node_t *nodes, int nNodes, int start)
{
  for (int i = 0; i < nNodes; i++) {
    nodes[i].distance = INFINITY;
  }
  int queue[MAX_NODES];
  int begin = 0;
  int end = 1;
  queue[begin] = start;
  nodes[start-1].distance = 0;

  while(begin < end) {
    printf("Popped node %d from stack.\n", queue[begin]);
    node_t node = nodes[queue[begin++]-1];
    
    for (int j = 0; j < nNodes; j++) {
      if (node.neighbours[j]) {
        int neighbourId = node.neighbours[j];
        nodes[neighbourId-1].distance = node.distance + 1;
        queue[end++] = neighbourId;
      }
      else
        break;
    }
  }
}

// Input format:
// * Node numbering starts at 1.
// * On the 1st line: {#nodes} {#root-node} <- we might require this to be 1
// * On each of the following #nodes lines: {#children} {child_1} ... {child_n}
int main()
{
  int nNodes, start;
  node_t* nodes = (node_t*)calloc(MAX_NODES, sizeof(node_t));
  
  if(nodes == 0) // calloc failed
    return 1;
    
  scanf("%d %d\n", &nNodes, &start);
  
  for (int i = 0; i < nNodes; i++) {
    int nChildren;
    scanf("%d", &nChildren);
    int j = 0;
    for (; j < nChildren; j++) {
      scanf("%d", &(nodes[i].neighbours[j]));
    }
    // mark the end
    nodes[i].neighbours[j] = 0;
  }
  
  bfs(nodes, nNodes, start);
  for (int i = 0; i < nNodes; i++) {
    printf("distance(%d) = %d\n", i, nodes[i].distance);
  }
  
  return 0;
}
