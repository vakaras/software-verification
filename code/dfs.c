/*
 * Proved: Each node in a “tree” is visited and the distance of the child
 * is bigger by one than the distance of the parent. Also proved that
 * the tree is left unchanged.
 */
struct node {
  int children_count;
  struct node *children;
  struct node *parent;
  int distance;
};

/*@

// The representation of the tree using inductive data types. subtree_i
// represents a tree, which root is node, and subtree_children_i
// represents a list of children nodes of that node. These data structures
// are needed for proving that the structure of the tree is not modified
// by the algorithm.

inductive subtree_children_i =  subtree_children_nil |
                                subtree_children_cons(
                                  subtree_i,
                                  subtree_children_i);

inductive subtree_i = subtree_cons(struct node *, subtree_children_i);

// Helper fixpoint functions and lemmas for working with inductive data
// types.

fixpoint subtree_children_i children_merge(
    subtree_children_i nodes1,
    subtree_children_i nodes2)
{
  switch (nodes1) {
    case subtree_children_nil: return nodes2;
    case subtree_children_cons(parent, parent_children_nodes):
      return subtree_children_cons(
                        parent,
                        children_merge(parent_children_nodes, nodes2));
  }
}

lemma void children_merge_associative(
    subtree_children_i nodes1,
    subtree_children_i nodes2,
    subtree_children_i nodes3)
  requires  emp;
  ensures   (children_merge(children_merge(nodes1, nodes2), nodes3) ==
            children_merge(nodes1, children_merge(nodes2, nodes3)));
{
  switch (nodes1) {
    case subtree_children_nil:
      return;
    case subtree_children_cons(node, tail):
      children_merge_associative(tail, nodes2, nodes3);
      return;
  }
}

lemma void children_merge_nil(subtree_children_i nodes)
 requires emp;
 ensures children_merge(nodes, subtree_children_nil) == nodes;
{
 switch (nodes) {
   case subtree_children_nil: return;
   case subtree_children_cons(node, tail): children_merge_nil(tail); return;
 }
}

// Predicates that expresses the fact that the tree starting at node
// node is unvisited.

predicate unvisited_node_p(
    struct node *node,
    int children_count,
    struct node *children,
    subtree_i subtree,
    struct node *parent,
    int distance) =
  node != 0 &*&
  node->children_count |-> children_count &*&
  children_count >= 0 &*&
  node->children |-> children &*&
  unvisited_children_p(children, children_count, ?children_nodes) &*&
  subtree == subtree_cons(node, children_nodes) &*&
  node->parent |-> parent &*&
  parent == 0 &*&
  node->distance |-> distance &*&
  distance == -1;

predicate unvisited_child_p(struct node *child, subtree_i subtree) =
  child != 0 &*&
  unvisited_node_p(child, _, _, subtree, _, _);

predicate unvisited_children_p(
    struct node *start,
    int count,
    subtree_children_i children_nodes) =
  count == 0 ?
  children_nodes == subtree_children_nil :
  unvisited_child_p(start, ?start_subtree) &*&
  unvisited_children_p(start + 1, count - 1, ?children_nodes_left) &*&
  children_nodes == subtree_children_cons(start_subtree, children_nodes_left);

// Predicates that expresses the fact that the node is being analysed now.

predicate visiting_node_p(
    struct node *node,
    int children_count,
    struct node *children,
    subtree_i subtree,
    struct node *parent,
    int distance) =
  node != 0 &*&
  node->children_count |-> children_count &*&
  children_count >= 0 &*&
  node->children |->children &*&
  unvisited_children_p(children, children_count, ?children_nodes) &*&
  subtree == subtree_cons(node, children_nodes) &*&
  node->parent |-> parent &*&
  node->distance |-> distance;

// Predicates that expresses the fact that the tree starting at node
// node is visited.

predicate visited_node_p(
    struct node *node,
    int children_count,
    struct node *children,
    subtree_i subtree,
    struct node *parent,
    int distance) =
  node != 0 &*&
  node->children_count |-> children_count &*&
  children_count >= 0 &*&
  node->children |->children &*&
  visited_children_p(children, children_count, ?children_nodes,
                     node, distance + 1) &*&
  subtree == subtree_cons(node, children_nodes) &*&
  node->parent |-> parent &*&
  node->distance |-> distance;

predicate visited_child_p(
    struct node *child,
    struct node *parent,
    int distance,
    subtree_i subtree) =
  child == 0 ?
  emp :
  visited_node_p(child, _, _, subtree, parent, distance);

predicate visited_children_p(
    struct node *start,
    int count,
    subtree_children_i children_nodes,
    struct node *parent,
    int distance) =
  count == 0 ?
  children_nodes == subtree_children_nil :
  visited_child_p(start, parent, distance, ?start_subtree) &*&
  visited_children_p(start + 1, count - 1, ?children_nodes_left,
                     parent, distance) &*&
  children_nodes == subtree_children_cons(start_subtree, children_nodes_left);

// Helper lemmas.

lemma void visited_children_append(
    struct node *children,
    int count)
  requires  visited_children_p(children, count, ?children_nodes,
                               ?parent, ?depth) &*&
            visited_child_p(children + count, parent, depth, ?subtree) &*&
            count >= 0;
  ensures   visited_children_p(
              children, count + 1,
              children_merge(
                children_nodes,
                subtree_children_cons(subtree, subtree_children_nil)),
              parent, depth);
{
  open visited_children_p(children, count, children_nodes, parent, depth);
  if (count == 0) {
    close visited_children_p(children + 1, 0, subtree_children_nil,
                             parent, depth);
  } else {
    visited_children_append(children + 1, count - 1);
  }
  close visited_children_p(children, count + 1, _, parent, depth);
}

@*/

/*
 * This function recursively visits the subtree, which root node is node.
 *
 * It sets the node->parent pointer to point to the parent of the node and
 * sets node->distance = node->parent->distance + 1.
 */
void dfs_worker(struct node *node, int depth)
  /*@ requires  depth >= 0 &*&
                visiting_node_p(node, ?node_children_count,
                                ?node_children, ?node_subtree,
                                ?parent, depth);
  @*/
  /*@ ensures   visited_node_p(node, node_children_count,
                               node_children, node_subtree,
                               parent, depth);
  @*/
{
  /*@ open visiting_node_p(node, node_children_count,
                           node_children, node_subtree,
                           parent, depth);
  @*/
  int children_count = node->children_count;
  struct node *children = node->children;
  if (children_count == 0) {
    //@ open unvisited_children_p(children, 0, ?subtree_children);
    //@ assert(node_subtree == subtree_cons(node, subtree_children_nil));
    /*@ close visited_children_p(
          children, 0, subtree_children_nil, node, depth + 1);
    @*/
    //@ close visited_node_p(node, _, _, node_subtree, _, depth);
  } else {
    /*@ open unvisited_children_p(children, node_children_count,
                                  ?subtree_children);
    @*/
    /*@ close unvisited_children_p(children, node_children_count,
                                   subtree_children);
    @*/
    //@ assert(node_subtree != subtree_cons(node, subtree_children_nil));
    int i = 0;
    /*@ close visited_children_p(
          children, 0, subtree_children_nil, node, depth + 1);
    @*/
    for (; i != children_count; i++)
      /*@ invariant unvisited_children_p(
                      children + i, children_count - i, ?children_nodes1) &*&
                    visited_children_p(
                      children, i, ?children_nodes2, node, depth + 1) &*&
                    (children_merge(children_nodes2, children_nodes1) ==
                      subtree_children) &*&
                    i >= 0;
      @*/
    {
      /*@ open unvisited_children_p(children + i, children_count - i,
                                    children_nodes1);
      @*/
      /*@ open unvisited_children_p(children + i + 1, children_count - i - 1,
                                    ?children_nodes1_left);
      @*/
      /*@ close unvisited_children_p(children + i + 1, children_count - i - 1,
                                     children_nodes1_left);
      @*/
      struct node *child = children + i;
      //@ open unvisited_child_p(child, ?child_subtree);
      //@ open unvisited_node_p(child, _, _, child_subtree, _, _);
      child->parent = node;
      child->distance = depth + 1;
      //@ close visiting_node_p(child, _, _, _, node, depth + 1);
      dfs_worker(child, depth + 1);
      //@ close visited_child_p(child, node, depth + 1, child_subtree);
      //@ visited_children_append(children, i);
      /*@ children_merge_associative(
            children_nodes2,
            subtree_children_cons(child_subtree, subtree_children_nil),
            children_nodes1_left);
      @*/
    }
    /*@ open visited_children_p(
                      children, i, ?children_nodes2, node, depth + 1);
    @*/
    /*@ close visited_children_p(
                      children, i, children_nodes2, node, depth + 1);
    @*/
    /*@ open unvisited_children_p(children + i,
                                  children_count - i,
                                  ?children_nodes1);
    @*/
    //@ children_merge_nil(children_nodes2);
    //@ assert(children_nodes2 == subtree_children);
    assert(children_count - i == 0);
    //@ close visited_node_p(node, _, _, node_subtree, _, depth);
  }
}

/*
 * This function recursively visits the subtree, which root node is node.
 */
void dfs(struct node *node)
  /*@ requires  unvisited_node_p(node, ?node_children_count,
                                 ?node_children, ?node_subtree,
                                 _, _);
  @*/
  /*@ ensures   visited_node_p(node, node_children_count,
                               node_children, node_subtree,
                               0, 0);
  @*/
{
  /*@ open unvisited_node_p(node, node_children_count,
                            node_children, node_subtree,
                            _, _);
  @*/
  node->parent = 0;
  node->distance = 0;
  /*@ close visiting_node_p(node, node_children_count,
                            node_children, node_subtree,
                            0, 0);
  @*/
  dfs_worker(node, 0);
}
