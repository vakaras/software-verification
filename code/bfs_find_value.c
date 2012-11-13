#include <stdio.h>
#include <stdlib.h>

#define MAX_NODES 1000
#define INFINITY 100000

#define FALSE 0
#define TRUE  1
typedef int BOOL

struct node {
  struct node* neighbours[MAX_NODES];
  int value;
  int distance;
};
typedef struct node node_t;

BOOL bfs_find_value(node_t* startNode, value, int* out_distance)
{
  for (int i = 0; i < nNodes; i++) {
    nodes[i].distance = INFINITY;
  }
  node_t* queue[MAX_NODES];
  int begin = 0;
  int end = 1;
  queue[begin] = startNode;
  startNode->distance = 0;

  while(begin < end) {
    //printf("Popped node %d from stack.\n", queue[begin]);
    node_t* node = queue[begin++];
    
    for (int j = 0; j < nNodes; j++) {
      if (node->neighbours[j]) {
        node_t* neighbour = node.neighbours[j];
        neighbour->distance = node->distance + 1;
        
        if(neighbour->value == value)
        {
          *out_distance = neighbour->distance;
          return TRUE;
        }
        
        queue[end++] = neighbour;
      }
      else
        break;
    }
  }
  
  return FALSE;
}
