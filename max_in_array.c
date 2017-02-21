/*@ requires size > 0;
    requires \valid(a+(0..size-1));
    requires \valid(max);
    requires \valid(min);
    assigns *min, *max;
    ensures 0 <= *min < size;
    ensures 0 <= *max < size;
    behavior max:
      ensures \forall integer i; (0 <= i <size) && (i % 2 == 0) == > a[*max] >= a[i];
    behavior min:
        ensures \forall integer i; (0 <= i <size) && (i % 2 == 1) == > a[*min] <= a[i];
 */
int min_max_in_array(int *a, int size, int* min, int* max)
{
    int max = 0;
    int min = 1;
    /*@
     loop invariant 2 <= i <= size;
     loop invariant 0 <= max < i;
     loop invariant 0 <= min < i;
     loop invariant max % 2 == 0;
     loop invariant min % 2 == 1;
     loop invariant \forall integer k; (0 <= k <size) && (k % 2 == 0) == > a[*max] >= a[k];
     loop invariant \forall integer k; (0 <= k <size) && (k % 2 == 1) == > a[*min] <= a[k];
     loop variant size - i;
     */
    for(int i = 2; i < size; i+=2)
    {
      if (i % 2 == 0)
      {
        if(a[max] >= a[i] )
        {
          max = i;
        }
      }
      else{
        if(a[min] <= a[i])
        {
            min = i;
        }
    }
}
