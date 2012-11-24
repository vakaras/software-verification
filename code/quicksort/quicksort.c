// quicksort.c

/*@

predicate unsorted_array(int* a, int count) = count <= 0 ? true
  : integer(a, _) &*& unsorted_array(a + 1, count - 1);


lemma void split_unsorted_array(int* a, int j)
  requires unsorted_array(a, ?count) &*& 0 <= j &*& j <= count;
  ensures unsorted_array(a, j) &*& unsorted_array(a + j, count - j);
{
  if(j == 0)
    close unsorted_array(a, 0);
  else
  {
    open unsorted_array(a, count);
    split_unsorted_array(a + 1, j - 1);
    close unsorted_array(a, j);
  }
}

@*/

void quicksort(int* array, int array_count)
//@ requires unsorted_array(array, array_count) &*& array_count > 0;
//@ ensures true;
{
  subsort(array, 0, array_count - 1);
}

void subsort(int* array, int first_index, int last_index)
//@ requires unsorted_array(array + first_index, last_index - first_index + 1) &*& first_index >= 0 &*& last_index >= first_index;
//@ ensures true;
{
  if(first_index < last_index)
  {
    int partition_index = partition(array, first_index, last_index);
    //@ split_unsorted_array(array + first_index, partition_index);
    subsort(array, first_index, partition_index - 1);
    subsort(array, partition_index, last_index);
  }
}

int partition(int* array, int first_index, int last_index)
//@ requires unsorted_array(array + first_index, last_index - first_index + 1);
//@ ensures unsorted_array(array + first_index, last_index - first_index + 1) &*& first_index <= result &*& result <= last_index;
{
  int x = array[last_index];
  int i = first_index - 1;
  for(int j = first_index; j < last_index; j++)
  {
    if(array[j] <= x)
    {
      i++;
      swap(&(array[i]), &(array[j]));
    }
  }
  swap(&(array[i + 1]), &(array[last_index]));
  
  return (i + 1);
}

void swap(int* a, int* b)
//@ requires true;
//@ ensures true;
{
  int temp = *a;
  *a = *b;
  *b = temp;
}
