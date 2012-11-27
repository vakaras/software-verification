#include "malloc.h"
#include "stdlib.h"

/*
 * Prooved: Each node in a “tree” is visited and the distance of the child
 * is bigger by one than the distance of the parent.
 */
struct node {
  int children_count;
  struct node *children;
  struct node *parent;
  int distance;
};

struct queue_node {
  struct node *node;
  struct queue_node *next;
};

struct queue {
  int length;
  struct queue_node *first;
};

/*@

predicate unvisited_node_p(
    struct node *node,
    int children_count,
    struct node *children,
    struct node *parent,
    int distance) =
  node != 0 &*&
  node->children_count |-> children_count &*&
  children_count >= 0 &*&
  node->children |-> children &*&
  unvisited_children_p(children, children_count) &*&
  node->parent |-> parent &*&
  parent == 0 &*&
  node->distance |-> distance &*&
  distance == -1;

predicate unvisited_child_p(struct node *child) =
  child != 0 &*&
  unvisited_node_p(child, _, _, _, _);

predicate unvisited_children_p(struct node *start, int count) =
  count == 0 ?
  emp :
  unvisited_child_p(start) &*&
  unvisited_children_p(start + 1, count - 1);

predicate visiting_node_p(
    struct node *node,
    int children_count,
    struct node *children,
    struct node *parent,
    int distance) =
  node != 0 &*&
  node->children_count |-> children_count &*&
  children_count >= 0 &*&
  node->children |->children &*&
  unvisited_children_p(children, children_count) &*&
  node->parent |-> parent &*&
  node->distance |-> distance;

predicate visited_node_p(
    struct node *node,
    int children_count,
    struct node *children,
    struct node *parent,
    int distance) =
  node != 0 &*&
  node->children_count |-> children_count &*&
  children_count >= 0 &*&
  node->children |->children &*&
  visited_children_p(children, children_count, node, distance + 1) &*&
  node->parent |-> parent &*&
  node->distance |-> distance;

predicate visited_child_p(
    struct node *child,
    struct node *parent,
    int distance) =
  child == 0 ?
  emp :
  visited_node_p(child, _, _, parent, distance);

predicate visited_children_p(
    struct node *start,
    int count,
    struct node *parent,
    int distance) =
  count == 0 ?
  emp :
  visited_child_p(start, parent, distance) &*&
  visited_children_p(start + 1, count - 1, parent, distance);

lemma void visited_children_append(
    struct node *children,
    int count)
  requires  visited_children_p(children, count, ?parent, ?depth) &*&
            visited_child_p(children + count, parent, depth) &*&
            count >= 0;
  ensures   visited_children_p(children, count + 1, parent, depth);
{
  open visited_children_p(children, count, parent, depth);
  if (count == 0) {
    close visited_children_p(children + 1, 0, parent, depth);
  } else {
    visited_children_append(children + 1, count - 1);
  }
  close visited_children_p(children, count + 1, parent, depth);
}

predicate visiting_node_queue_node_p(
    struct queue_node *queue_node,
    int count) =
  count == 0 ?
  queue_node == 0 :
  queue_node != 0 &*&
  malloc_block_queue_node(queue_node) &*&
  queue_node->node |-> ?node &*&
  node != 0 &*&
  visiting_node_p(node, _, _, _, _) &*&
  queue_node->next |-> ?next &*&
  visiting_node_queue_node_p(next, count - 1);

predicate visiting_node_queue_p(
    struct queue *queue,
    int count) =
  queue->first |-> ?first &*&
  queue->length |-> count &*&
  count >= 0 &*&
  visiting_node_queue_node_p(first, count);

@*/

void dfs_worker(struct node *node, int depth)
  /*@ requires  depth >= 0 &*&
                visiting_node_p(node, ?node_children_count,
                                ?node_children, ?parent, depth);
  @*/
  /*@ ensures   visited_node_p(node, node_children_count,
                               node_children, parent, depth);
  @*/
{
  /*@ open visiting_node_p(node, node_children_count,
                           node_children, parent, depth);
  @*/
  int children_count = node->children_count;
  struct node *children = node->children;
  int i = 0;
  //@ close visited_children_p(children, 0, node, depth + 1);
  for (; i != children_count; i++)
    /*@ invariant unvisited_children_p(children + i, children_count - i) &*&
                  visited_children_p(children, i, node, depth + 1) &*&
                  i >= 0;
    @*/
  {
    //@ open unvisited_children_p(children + i, children_count - i);
    struct node *child = children + i;
    //@ open unvisited_child_p(child);
    //@ open unvisited_node_p(child, _, _, _, _);
    child->parent = node;
    child->distance = depth + 1;
    //@ close visiting_node_p(child, _, _, node, depth + 1);
    dfs_worker(child, depth + 1);
    //@ close visited_child_p(child, node, depth + 1);
    //@ visited_children_append(children, i);
  }
  assert(children_count - i == 0);
  //@ open unvisited_children_p(children + i, children_count - i);
  //@ close visited_node_p(node, _, _, _, depth);
}

struct queue_node *queue_append_worker(
    struct queue_node *queue_node,
    struct node *node,
    int length)
  /*@ requires  visiting_node_queue_node_p(queue_node, length) &*&
                visiting_node_p(node, _, _, _, _) &*&
                node != 0 &*&
                length >= 0;
  @*/
  /*@ ensures   visiting_node_queue_node_p(result, length + 1) &*&
                result != 0;
  @*/ 
{
  struct queue_node *tmp;
  //@ open visiting_node_queue_node_p(queue_node, length);
  if (length == 0)
  {
    assert(queue_node == 0);
    tmp = malloc(sizeof(struct queue_node));
    if (tmp == 0) {
      abort();
    }
    tmp->node = node;
    tmp->next = 0;
    //@close visiting_node_queue_node_p(0, 0);
    //@close visiting_node_queue_node_p(tmp, 1);
    return tmp;
  } else {
    tmp = queue_append_worker(queue_node->next, node, length - 1);
    queue_node->next = tmp;
    assert(queue_node != 0);
    //@close visiting_node_queue_node_p(queue_node, length + 1);
    return queue_node;
  }
}

void queue_append(struct queue *queue, struct node *node)
  /*@ requires  visiting_node_queue_p(queue, ?count) &*&
                node != 0 &*&
                visiting_node_p(node, _, _, _, _);
  @*/
  /*@ ensures   visiting_node_queue_p(queue, count + 1);
  @*/ 
{
  struct queue_node *tmp;
  //@ open visiting_node_queue_p(queue, count);
  //@ assert(count == queue->length);
  tmp = queue_append_worker(queue->first, node, queue->length);
  queue->first = tmp;
  queue->length++;
  //@ close visiting_node_queue_p(queue, count + 1);
}

struct node *queue_pop(struct queue *queue)
  /*@ requires  visiting_node_queue_p(queue, ?count) &*&
                count > 0;
  @*/
  /*@ ensures   visiting_node_queue_p(queue, count - 1) &*&
                result != 0 &*&
                visiting_node_p(result, _, _, _, _);
  @*/
{
  struct queue_node *tmp;
  //@ open visiting_node_queue_p(queue, count);
  tmp = queue->first;
  struct node *node;
  //@ open visiting_node_queue_node_p(tmp, count);
  node = tmp->node;
  queue->first = tmp->next;
  queue->length--;
  free(tmp);
  //@ close visiting_node_queue_p(queue, count-1);
  return node;
}

//void bfs(struct node *node, struct node **queue, int queue_size)
//  /*@ requires  unvisited_node_p(node, ?node_children_count,
//                                ?node_children, _, _) &*&
//                visiting_node_queue_p(queue, queue_size) &*&
//                queue_size > 0;
//  @*/
//  /*@ ensures   visited_node_p(node, node_children_count,
//                               node_children, 0, 0);
//  @*/
//{
//  //@ open unvisited_node_p(node, node_children_count, node_children, _, _);
//  node->parent = 0;
//  node->distance = 0;
//  //@ close visiting_node_p(node, node_children_count, node_children, 0, 0);
//  int begin = 0;
//  int end = 0;
//  *(queue + end) = node;
//  //@ visiting_node_queue_append(queue + begin, node);
//}
