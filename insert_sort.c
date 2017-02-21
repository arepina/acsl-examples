

/*@
*/
void insert_sort(int t[], int n)
{
  int i, j;
  int mv;
  if (n <= 1) return;
  /*@ loop invariant 0 <= i < n;
  loop invariant Sorted(t, 0, i);
  loop variant n - i;
  */
  for(i = 1; i < n; i++)
  {
    mv = t[i];
    /*@ loop invariant 0 <= j <= i;
      loop invariant j == i ==> Sorted(t,0,i);
      loop invariant j < i ==> Sorted (t, 0, i+1);
      loop invariant \forall integer k; j <= k < i ==> t[k] >mv;
      loop variant j;
    */
    for(j = i; j >= 0; j--)
    {
      if (t[j - 1] <= mv) break;
      t[j] = t[j-1];
    }
    t[j] = mv;
  }
}
