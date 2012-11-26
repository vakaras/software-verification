/*
 * Prooved: Each node in a “tree” is visited and the distance of the child
 * is bigger by one than the distance of the parent.
 */
struct node {
  struct node *child_left;
  struct node *child_right;
  struct node *parent;
  int distance;
};

/*@

predicate unvisited_node_p(
    struct node *node,
    struct node *child_left,
    struct node *child_right,
    struct node *parent,
    int distance) =
  node != 0 &*&
  node->child_left |-> child_left &*&
  unvisited_child_p(child_left) &*&
  node->child_right |-> child_right &*&
  unvisited_child_p(child_right) &*&
  node->parent |-> parent &*&
  parent == 0 &*&
  node->distance |-> distance &*&
  distance == -1;

predicate unvisited_child_p(struct node *child) =
  child == 0 ?
  emp :
  unvisited_node_p(child, _, _, _, _);

predicate visiting_node_p(
    struct node *node,
    struct node *child_left,
    struct node *child_right,
    struct node *parent,
    int distance) =
  node != 0 &*&
  node->child_left |-> child_left &*&
  unvisited_child_p(child_left) &*&
  node->child_right |-> child_right &*&
  unvisited_child_p(child_right) &*&
  node->parent |-> parent &*&
  node->distance |-> distance;

predicate visited_node_p(
    struct node *node,
    struct node *child_left,
    struct node *child_right,
    struct node *parent,
    int distance) =
  node != 0 &*&
  node->child_left |-> child_left &*&
  visited_child_p(child_left, node, distance + 1) &*&
  node->child_right |-> child_right &*&
  visited_child_p(child_right, node, distance + 1) &*&
  node->parent |-> parent &*&
  node->distance |-> distance;

predicate visited_child_p(
    struct node *child,
    struct node *parent,
    int distance) =
  child == 0 ?
  emp :
  visited_node_p(child, _, _, parent, distance);

@*/

void dfs(struct node *node, int depth)
  /*@ requires  depth >= 0 &*&
                visiting_node_p(node, ?node_child_left, ?node_child_right,
                                ?parent, depth);
  @*/
  /*@ ensures   visited_node_p(node, node_child_left, node_child_right,
                               parent, depth);
  @*/
{
  //@ open visiting_node_p(node, node_child_left, node_child_right, parent, depth);
  struct node *child_left = node->child_left;
  //@ open unvisited_child_p(child_left);
  if (child_left != 0) {
    //@ open unvisited_node_p(child_left, _, _, _, _);
    child_left->parent = node;
    child_left->distance = depth + 1;
    //@ close visiting_node_p(child_left, _, _, _, _);
    dfs(child_left, depth + 1);
  }
  //@ close visited_child_p(child_left, node, depth + 1);
  struct node *child_right = node->child_right;
  //@ open unvisited_child_p(child_right);
  if (child_right != 0) {
    //@ open unvisited_node_p(child_right, _, _, _, _);
    child_right->parent = node;
    child_right->distance = depth + 1;
    //@ close visiting_node_p(child_right, _, _, _, _);
    dfs(child_right, depth + 1);
  }
  //@ close visited_child_p(child_right, node, depth + 1);
  //@ close visited_node_p(node, _, _, _, depth);
}
