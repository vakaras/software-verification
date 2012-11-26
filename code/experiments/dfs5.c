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

void dfs(struct node *node)
  /*@ requires  unvisited_node_p(node, ?node_children_count,
                                ?node_children, _, _);
  @*/
  /*@ ensures   visited_node_p(node, node_children_count,
                               node_children, 0, 0);
  @*/
{
  //@ open unvisited_node_p(node, node_children_count, node_children, _, _);
  node->parent = 0;
  node->distance = 0;
  //@ close visiting_node_p(node, node_children_count, node_children, 0, 0);
  dfs_worker(node, 0);
}
