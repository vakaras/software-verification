struct node {
  struct node *child;
  struct node *parent;
  int distance;
};

/*@

predicate unvisited_node_p(
    struct node *node,
    struct node *child,
    struct node *parent,
    int distance) =
  node != 0 &*&
  node->child |-> child &*&
  unvisited_child_p(child) &*&
  node->parent |-> parent &*&
  parent == 0 &*&
  node->distance |-> distance &*&
  distance == -1;

predicate unvisited_child_p(struct node *child) =
  child == 0 ?
  emp :
  unvisited_node_p(child, _, _, _);

predicate visiting_node_p(
    struct node *node,
    struct node *child,
    struct node *parent,
    int distance) =
  node != 0 &*&
  node->child |-> child &*&
  unvisited_child_p(child) &*&
  node->parent |-> parent &*&
  node->distance |-> distance;

predicate visited_node_p(
    struct node *node,
    struct node *child,
    struct node *parent,
    int distance) =
  node != 0 &*&
  node->child |-> child &*&
  visited_child_p(child, node) &*&
  node->parent |-> parent &*&
  node->distance |-> distance;

predicate visited_child_p(struct node *child, struct node *parent) =
  child == 0 ?
  emp :
  visited_node_p(child, _, parent, _);

@*/

void dfs(struct node *node, int depth)
  /*@ requires  depth >= 0 &*&
                visiting_node_p(node, ?node_child, ?parent, depth);
  @*/
  /*@ ensures   visited_node_p(node, node_child, parent, depth);
  @*/
{
  //@ open visiting_node_p(node, node_child, parent, depth);
  struct node *child = node->child;
  if (child != 0) {
    //@ open unvisited_child_p(child);
    //@ open unvisited_node_p(child, _, _, _);
    child->parent = node;
    child->distance = depth + 1;
    //@ close visiting_node_p(child, _, _, _);
    dfs(child, depth + 1);
    //@ close visited_child_p(child, node);
    //@ close visited_node_p(node, _, _, _);
  } else {
    //@ open unvisited_child_p(child);
    //@ close visited_child_p(child, node);
    //@ close visited_node_p(node, _, _, _);
  }
}
