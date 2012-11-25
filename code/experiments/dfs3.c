struct node;

struct list_node {
  struct list_node *next;
  struct node *node;
};

struct node {
  struct list_node *children;
  struct node *parent;
  int distance;
};


/*@

predicate child_p(
    struct list_node *container,
    struct list_node *next,
    struct node *node) =
  container->next |-> next &*&
  container->node |-> node &*&
  container != 0;

inductive children_i  = children_nil |
                        children_cons(struct node *, children_i);

predicate children_p(struct list_node *container, children_i children) =
  container == 0 ?
  children == children_nil :
  child_p(container, ?next, ?node) &*&
  node_p(node, _) &*&
  children_p(next, ?tail) &*&
  children == children_cons(node, tail);

predicate node_p(
    struct node *node,
    children_i children) =
  node != 0 &*&
  node->children |-> ?container &*&
  children_p(container, children) &*&
  node->parent |-> ?parent_null &*&
  parent_null == 0 &*&
  node->distance |-> ?distance_null &*&
  distance_null == -1;

inductive parents_i = parents_nil |
                      parents_cons(struct node *, int, parents_i);

predicate parents_p(
    struct node *node,
    int distance,
    parents_i parents,
    struct node *parent) =
  node == 0 ?
  parents == parents_nil &*&
  distance == -1 :
  node->parent |-> parent &*&
  node->distance |-> distance &*&
  parents_p(parent, ?parent_distance, ?parent_parents, ?parent_parent) &*&
  parents == parents_cons(node, distance, parent_parents) &*&
  parent_distance + 1 == distance;

@*/

/*@

predicate visited_child_p(
    struct list_node *container,
    struct list_node *next,
    struct node *node) =
  container->next |-> next &*&
  container->node |-> node &*&
  container != 0;

predicate visited_children_p(struct list_node *container, children_i children) =
  container == 0 ?
  children == children_nil :
  visited_child_p(container, ?next, ?node) &*&
  visited_node_p(node, _, _, _) &*&
  visited_children_p(next, ?tail) &*&
  children == children_cons(node, tail);

//lemma void visited_children_append(
//    struct list_node *start,
//    struct list_node *new)
//  requires  visited_children_p(start, ?children) &*&
//            visited_child_p(new, ?next, ?node) &*&
//            visited_node_p(node, _, _, _) &*&
//            start != 0;
//  ensures   visited_children_p(start, ?visited_children);
//{
//  // TODO: Ensure that “new” was actually appended.
//  open visited_children_p(start, children);
//  switch (children) {
//    case children_nil:
//      open visited_child_p(new, next, node);
//      close visited_children_p(new->next, children_nil);
//  }
//open visited_child_p(start, ?start_next, ?start_node);
//if (start_next == new) {
//  open visited_child_p(new, next, node);
//  close visited_children_p(new->next, children_nil);
//  close visited_child_p(new, next, node);
//  close visited_children_p(new, children_cons(node, children_nil));
//} else {
//  visited_children_append(start->next, new);
//  close visited_children_p(start, _);
//}
//}
  
predicate visited_node_p(
    struct node *node,
    children_i children,
    parents_i parents,
    int distance) =
  node != 0 &*&
  node->children |-> ?container &*&
  visited_children_p(container, children) &*&
  node->distance |-> distance &*&
  node->parent |-> ?parent &*&
  parents_p(parent, distance - 1, parents, _);

@*/


void dfs_worker(struct node *root, int depth, struct node *parent)
  /*@ requires  depth >= 0 &*&
                node_p(root, ?children) &*&
                parents_p(parent, depth - 1, ?parents, ?parent_parent);
  @*/
  /*@ ensures   visited_node_p(root, ?visited_children,
                               parents_cons(root, depth, parents), depth) &*&
                children == visited_children &*&
                parents_p(parent, depth - 1, parents, parent_parent);
  @*/
{
  //@ open node_p(root, children);
  root->distance = depth;
  root->parent = parent;
  struct list_node *container = root->children;
  struct list_node *new_list = 0;
  //@ close visited_children_p(new_list, children_nil);
  while (container != 0)
    /*@ invariant 
                  children_p(container, ?children_loop) &*&
                  root->distance |-> depth &*&
                  root->parent |-> parent &*&
                  parents_p(parent, depth - 1, parents, _) &*&
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
  //@ close parents_p(root, depth, parents_cons(root, depth, parents), parent);
  //@ open children_p(container, _);
  root->children = new_list;
  //@ close visited_node_p(root, _, parents_cons(root, depth, parents), depth);
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

