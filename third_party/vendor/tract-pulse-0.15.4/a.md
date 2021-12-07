


        |       |
 * * * * * * * * * *
 ----v
     * * * * * * * *

---S---> conv ---S-2-->
---4---> delay+overlap:2 --6,delay:2--> conv --4,delay:2--> 
* * 0 1 2 3
2 3 4 5 6 7

       |       |
* * * * * * * * * * * *

* * * * * * * *
                * * * *


--S--> pad(2) --> S + 4
--3--> delay:2 --3,d=2--> pad --> 3,d=0
                  **0               PP0


* * * | * * * | * * * | * *

* * * | * * * | * * * | * * * | *
  * * | * * * | * * * | * * * | * *
    * | * * * | * * * | * * * | * * *



pulse = 3
--S--> deconv  --S+2-->
                          deconv --3-->


* deconv: implemented by gemm + deconv_sum
* where to put the memory ?
   * before gemm: overlapping product will be done twice
   * between gemm and deconv_sum, maybe as a delay (?), big buffer, gemm unchanged
   * inside deconv_sum: instead of starting from zero, keep partial sums from one pass to the next
   * after deconv_sum: do not change the deconv sum, but use crop + delay + Add (?) to fix overlaps
