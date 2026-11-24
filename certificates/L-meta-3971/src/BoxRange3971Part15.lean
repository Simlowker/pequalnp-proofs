import Boxes3971Part15
import Catalog3971
namespace PetersenNegated3971
theorem boxRange15 (r : Fin 32) : let idx := 480+r.val
  checkBox (bk idx,bm idx,br idx)=true := by
  fin_cases r
  · exact box_ok480
  · exact box_ok481
  · exact box_ok482
  · exact box_ok483
  · exact box_ok484
  · exact box_ok485
  · exact box_ok486
  · exact box_ok487
  · exact box_ok488
  · exact box_ok489
  · exact box_ok490
  · exact box_ok491
  · exact box_ok492
  · exact box_ok493
  · exact box_ok494
  · exact box_ok495
  · exact box_ok496
  · exact box_ok497
  · exact box_ok498
  · exact box_ok499
  · exact box_ok500
  · exact box_ok501
  · exact box_ok502
  · exact box_ok503
  · exact box_ok504
  · exact box_ok505
  · exact box_ok506
  · exact box_ok507
  · exact box_ok508
  · exact box_ok509
  · exact box_ok510
  · exact box_ok511
end PetersenNegated3971
