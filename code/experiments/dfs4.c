struct node {
  struct int children_count;
  struct node **children;
  struct node *parent;
  int distance;
};

/*@
 
inductive children_i  = children_nil |
                        children_cons(struct node *, children_i);

predicate unvisited_node_p(
    struct node *node,
    int children_count,
    children_i children,
    parents_i parents,
    struct node *parent,
    int distance) =
  node != 0 &*&
  node->children_count |-> children_count &*&
  node->children |-> ?children_start &*&
  unvisited_children_p(children_start, children_count, children) &*&
  node->distance |-> distance &*&
  node->parent |-> parent &*&
  parent == parents_head(parents);
  
predicate visited_node_p(
    struct node *node,
    children_i children,
    parents_i parents,
    struct node *parent,
    int distance) =
  node != 0 &*&
  node->children |-> ?container &*&
  visited_children_p(container, children) &*&
  node->distance |-> distance &*&
  node->parent |-> parent &*&
  parent == parents_head(parents);

@*/


void dfs_worker(struct node *root, int depth)
  /*@ requires  depth >= 0 &*&
                unvisited_node_p(root, ?children, ?parents, ?parent, depth);
  @*/
  /*@ ensures   visited_node_p(root, children, parents, parent, depth);
  @*/
{
  //@ open node_p(root, children);
  struct list_node *container = root->children;
  //@ close visited_children_p(new_list, children_nil);
  while (container != 0)
    /*@ invariant 
                  children_p(container, ?children_loop) &*&
                  root->distance |-> depth &*&
                  root->parent |-> parent &*&
                  parents_p(parent, depth - 1, parents, parent_parent) &*&
                  visited_children_p(new_list, ?visited_children_loop);
    @*/
  {
    //@ close parents_p(root, depth, parents_cons(root, depth, parents), parent);
    //@ open children_p(container, children_loop);
    //@ open child_p(container, ?next, ?node);
    struct node *child = container->node;
    //@ assert(child == node);
    dfs_worker(child, depth + 1, root);
    struct list_node *tmp = container->next;
    container->next = new_list;
    //@ close visited_child_p(container, new_list, node);
    new_list = container;
    //@ close visited_children_p(new_list, _);

    /// close children_p(container, children_loop);
    container = tmp;
    //@ open parents_p(root, depth, parents_cons(root, depth, parents), parent);
  }
  //@ open children_p(container, _);
  /// close parents_p(root, depth, parents_cons(root, depth, parents), parent);
  root->children = new_list;
  //@ open parents_p(parent, depth - 1, parents, parent_parent);
  //@ close visited_node_p(root, _, parents, parent, depth);
  //@ close parents_p(parent, depth - 1, parents, parent_parent);
}

void dfs(struct node *root)
  /*@ requires  true;
  @*/
  /*@ ensures   true;
  @*/
{
  root->distance = 0;
  root->parent = NULL;
  dfs_worker(root, 0);
}

/*
 * Prove that node->distance == node->parent->distance + 1;
 */

