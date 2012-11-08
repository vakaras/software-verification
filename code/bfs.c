#include <stdio.h>

#define MAX_NODES 1000
#define INFINITY 100000


struct node {
  int neighbours[MAX_NODES];
  int distance;
};
typedef struct node node_t;


void bfs(node_t *nodes, int n, int start)
{
  for (int i = 0; i < n; i++) {
    nodes[i].distance = INFINITY;
  }
  int queue[MAX_NODES];
  int begin = 0;
  int end = 1;
  queue[begin] = start;
  nodes[start].distance = 0;

  for (int i = 0; i < n; i++) {
    node_t *node = nodes + queue[begin++];
    for (int j = 0; j < n; j++) {
      if (node->neighbours[j]) {
        nodes[j].distance = node->distance + 1;
        queue[end++] = j;
      }
    }
  }
}

int main(int argc, char *argv[])
{
  int n, start;
  node_t nodes[MAX_NODES];
  scanf("%d %d\n", &n, &start);
  for (int i = 0; i < n; i++) {
    for (int j = 0; j < n; j++) {
      scanf("%d", &nodes[i].neighbours[j]);
    }
  }
  bfs(nodes, n, start);
  for (int i = 0; i < n; i++) {
    printf("distance(%d) = %d\n", i, nodes[i].distance);
  }
}
