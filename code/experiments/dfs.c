struct node {
  int *neighbours;
  int distance;
  int parent;
};
/*@

inductive neighbours_i =  neighbours_nil |
                          neighbours_cons(int, neighbours_i);

predicate neighbours_p(int *start, int count, neighbours_i values) =
  count == 0 ?
  values == neighbours_nil :
  integer(start, ?value) &*&
  (value == 0 || value == 1) &*&
  neighbours_p(start + 1, count - 1, ?values0) &*&
  values == neighbours_cons(value, values0);

inductive parents_i = parents_nil |
                      parents_cons(int, parents_i);

fixpoint int parents_count(parents_i values) {
  switch (values) {
    case parents_nil: return 0;
    case parents_cons(parent, values0): return parents_count(values0) + 1;
    }
}

fixpoint int parents_head(parents_i values) {
  switch (values) {
    case parents_nil: return -1;
    case parents_cons(parent, values0): return parent;
  }
}

inductive nodes_i = nodes_nil |
                    nodes_cons(struct node *, nodes_i);

predicate node_p(
  struct node *node,
  int distance,
  neighbours_i neighbours,
  int nNeighbours,
  parents_i parents) =
  node != 0 &*&
  node->distance == distance &*&
  neighbours_p(?neighbours_start, nNeighbours, ?neighbours0) &*&
  neighbours == neighbours0 &*&
  node->neighbours == neighbours_start &*&
  (distance == -1 || parents_count(parents) == distance) &*&
  (distance == -1 || parents_head(parents) == node->parent)
  ;

predicate nodes_p(
  struct node *start,
  int count,
  nodes_i values,
  int total_count) =
  count == 0 ?
  values == nodes_nil :
  node_p(start, _, _, total_count, _) &*&
  nodes_p(start + 1, count - 1, ?values0, total_count) &*&
  values == nodes_cons(start, values0);

lemma void nodes_append(struct node *start, struct node *new)
  requires  nodes_p(start, ?count, ?values1, ?total_count) &*&
            node_p(new, _, _, total_count, _) &*&
            new == start + count &*&
            count >= 0;
  ensures   nodes_p(start, count + 1, ?values2, total_count);
{
  open nodes_p(start, count, values1, total_count);
  if (count != 0) {
    nodes_append(start + 1, new);
    close nodes_p(start, count + 1, _, total_count);
  } else {
    close nodes_p(start + 1, 0, nodes_nil, total_count);
    close nodes_p(start + count, 1, nodes_cons(start + count, nodes_nil),
                  total_count);
  }
}

lemma void nodes_split_worker(
    struct node *start,
    int counter,
    int offset,
    int total_count)
  requires  nodes_p(start + offset - counter, total_count - (offset - counter),
                    ?values2, total_count) &*&
            nodes_p(start, offset - counter, ?values1, total_count) &*&
            counter >= 0 &*&
            offset >= 0 &*&
            counter <= offset &*&
            offset < total_count;
  ensures   nodes_p(start, offset, ?values3, total_count) &*&
            nodes_p(start + offset, total_count - offset,
                    ?values4, total_count);
{
  // TODO: Prove that values1 + values2 == values3 + values4;
  open nodes_p(start + offset - counter, total_count - (offset - counter),
               values2, total_count);
  if (counter == 0) {
    close nodes_p(start + offset - counter, total_count - (offset - counter),
                  values2, total_count);
  } else {
    nodes_append(start, start + offset - counter);
    nodes_split_worker(start, counter - 1, offset, total_count);
  }
}

lemma void nodes_split(
    struct node *start,
    int offset,
    int total_count)
  requires  nodes_p(start, total_count, ?values1, total_count) &*&
            offset >= 0 &*&
            offset < total_count;
  ensures   nodes_p(start + offset, total_count - offset, ?values2,
                    total_count) &*&
            nodes_p(start, offset, ?values3, total_count);
{
  close nodes_p(start, 0, nodes_nil, total_count);
  nodes_split_worker(start, offset, offset, total_count);
}

lemma void nodes_join(
    struct node *start,
    int offset,
    int total_count)
  requires  nodes_p(start + offset, total_count - offset, ?values1,
                    total_count) &*&
            nodes_p(start, offset, ?values2, total_count) &*&
            offset >= 0 &*&
            offset < total_count;
  ensures   nodes_p(start, total_count, ?values3, total_count);
{
  // TODO: Prove that values3 == values2 + values1;
  open nodes_p(start + offset, total_count - offset, values1, total_count);
  nodes_append(start, start + offset);
  if (offset + 1 == total_count) {
    open nodes_p(start + offset + 1, 0, _, total_count);
  } else {
    nodes_join(start, offset + 1, total_count);
  }
}


@*/
