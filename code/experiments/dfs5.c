/*
 * Prooved: Each node in a “tree” is visited and the distance of the child
 * is bigger by one than the distance of the parent. Also prooved that
 * children are unchanged.
 */
struct node {
  int children_count;
  struct node *children;
  struct node *parent;
  int distance;
};

/*@

inductive children_i =  children_nil |
                        children_cons(struct node *, children_i);

//fixpoint children_i children_append(
//  children_i children_nodes,
//  struct node *child)
//{
//  switch (children_nodes) {
//    case children_nil: return children_cons(child, children_nil);
//    case children_cons(parent, parent_children_nodes):
//      return children_cons(parent,
//                           children_append(parent_children_nodes, child));
//  }
//}

//fixpoint



//fixpoint children_i children_front(children_i nodes, int counter)
//{
//  if (counter > 0) {
//    return children_cons(children_front()<++>)<++>
//  }
//}

// proove: children_front(nodes, children_count) == nodes

fixpoint children_i children_merge(children_i nodes1, children_i nodes2)
{
  switch (nodes1) {
    case children_nil: return nodes2;
    case children_cons(parent, parent_children_nodes):
      return children_cons(parent,
                           children_merge(parent_children_nodes, nodes2));
  }
}

lemma void children_merge_associative(
    children_i nodes1,
    children_i nodes2,
    children_i nodes3)
  requires  emp;
  ensures   (children_merge(children_merge(nodes1, nodes2), nodes3) ==
            children_merge(nodes1, children_merge(nodes2, nodes3)));
{
  switch (nodes1) {
    case children_nil:
      return;
    case children_cons(node, tail):
      children_merge_associative(tail, nodes2, nodes3);
      return;
  }
}

lemma void children_merge_nil(children_i nodes)
 requires emp;
 ensures children_merge(nodes, children_nil) == nodes;
{
 switch (nodes) {
   case children_nil: return;
   case children_cons(node, tail): children_merge_nil(tail); return;
 }
}

predicate unvisited_node_p(
    struct node *node,
    int children_count,
    struct node *children,
    children_i children_nodes,
    struct node *parent,
    int distance) =
  node != 0 &*&
  node->children_count |-> children_count &*&
  children_count >= 0 &*&
  node->children |-> children &*&
  unvisited_children_p(children, children_count, children_nodes) &*&
  node->parent |-> parent &*&
  parent == 0 &*&
  node->distance |-> distance &*&
  distance == -1;

predicate unvisited_child_p(struct node *child) =
  child != 0 &*&
  unvisited_node_p(child, _, _, _, _, _);

predicate unvisited_children_p(
    struct node *start,
    int count,
    children_i children_nodes) =
  count == 0 ?
  children_nodes == children_nil :
  unvisited_child_p(start) &*&
  unvisited_children_p(start + 1, count - 1, ?children_nodes_left) &*&
  children_nodes == children_cons(start, children_nodes_left);

predicate visiting_node_p(
    struct node *node,
    int children_count,
    struct node *children,
    children_i children_nodes,
    struct node *parent,
    int distance) =
  node != 0 &*&
  node->children_count |-> children_count &*&
  children_count >= 0 &*&
  node->children |->children &*&
  unvisited_children_p(children, children_count, children_nodes) &*&
  node->parent |-> parent &*&
  node->distance |-> distance;

predicate visited_node_p(
    struct node *node,
    int children_count,
    struct node *children,
    children_i children_nodes,
    struct node *parent,
    int distance) =
  node != 0 &*&
  node->children_count |-> children_count &*&
  children_count >= 0 &*&
  node->children |->children &*&
  visited_children_p(children, children_count, children_nodes,
                     node, distance + 1) &*&
  node->parent |-> parent &*&
  node->distance |-> distance;

predicate visited_child_p(
    struct node *child,
    struct node *parent,
    int distance) =
  child == 0 ?
  emp :
  visited_node_p(child, _, _, _, parent, distance);

predicate visited_children_p(
    struct node *start,
    int count,
    children_i children_nodes,
    struct node *parent,
    int distance) =
  count == 0 ?
  children_nodes == children_nil :
  visited_child_p(start, parent, distance) &*&
  visited_children_p(start + 1, count - 1, ?children_nodes_left,
                     parent, distance) &*&
  children_nodes == children_cons(start, children_nodes_left);

lemma void visited_children_append(
    struct node *children,
    int count)
  requires  visited_children_p(children, count, ?children_nodes,
                               ?parent, ?depth) &*&
            visited_child_p(children + count, parent, depth) &*&
            count >= 0;
  ensures   visited_children_p(
              children, count + 1,
              children_merge(children_nodes,
                             children_cons(children + count, children_nil)),
              parent, depth);
{
  // TODO: Prove that returns an extended children list.
  open visited_children_p(children, count, children_nodes, parent, depth);
  if (count == 0) {
    close visited_children_p(children + 1, 0, children_nil, parent, depth);
  } else {
    visited_children_append(children + 1, count - 1);
  }
  close visited_children_p(children, count + 1, _, parent, depth);
}

@*/

void dfs_worker(struct node *node, int depth)
  /*@ requires  depth >= 0 &*&
                visiting_node_p(node, ?node_children_count,
                                ?node_children, ?node_children_nodes,
                                ?parent, depth);
  @*/
  /*@ ensures   visited_node_p(node, node_children_count,
                               node_children, node_children_nodes,
                               parent, depth);
  @*/
{
  /*@ open visiting_node_p(node, node_children_count,
                           node_children, node_children_nodes,
                           parent, depth);
  @*/
  int children_count = node->children_count;
  struct node *children = node->children;
  if (children_count == 0) {
    //@ open unvisited_children_p(children, 0, node_children_nodes);
    //@ assert(node_children_nodes == children_nil);
    /*@ close visited_children_p(
          children, 0, children_nil, node, depth + 1);
    @*/
    //@ close visited_node_p(node, _, _, children_nil, _, depth);
  } else {
    /*@ open unvisited_children_p(children, node_children_count,
                                  node_children_nodes);
    @*/
    /*@ close unvisited_children_p(children, node_children_count,
                                   node_children_nodes);
    @*/
    //@ assert(node_children_nodes != children_nil);
    int i = 0;
    /*@ close visited_children_p(
          children, 0, children_nil, node, depth + 1);
    @*/
    for (; i != children_count; i++)
      /*@ invariant unvisited_children_p(
                      children + i, children_count - i, ?children_nodes1) &*&
                    visited_children_p(
                      children, i, ?children_nodes2, node, depth + 1) &*&
                    (children_merge(children_nodes2, children_nodes1) ==
                      node_children_nodes) &*&
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
      //@ open unvisited_child_p(child);
      //@ open unvisited_node_p(child, _, _, _, _, _);
      child->parent = node;
      child->distance = depth + 1;
      //@ close visiting_node_p(child, _, _, _, node, depth + 1);
      dfs_worker(child, depth + 1);
      //@ close visited_child_p(child, node, depth + 1);
      //@ visited_children_append(children, i);
      /*@ children_merge_associative(children_nodes2,
                                     children_cons(child, children_nil),
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
    //@ assert(children_nodes2 == node_children_nodes);
    assert(children_count - i == 0);
    //@ close visited_node_p(node, _, _, node_children_nodes, _, depth);
  }
}

void dfs(struct node *node)
  /*@ requires  unvisited_node_p(node, ?node_children_count,
                                 ?node_children, ?node_children_nodes,
                                 _, _);
  @*/
  /*@ ensures   visited_node_p(node, node_children_count,
                               node_children, node_children_nodes,
                               0, 0);
  @*/
{
  /*@ open unvisited_node_p(node, node_children_count,
                            node_children, node_children_nodes,
                            _, _);
  @*/
  node->parent = 0;
  node->distance = 0;
  /*@ close visiting_node_p(node, node_children_count,
                            node_children, node_children_nodes,
                            0, 0);
  @*/
  dfs_worker(node, 0);
}
