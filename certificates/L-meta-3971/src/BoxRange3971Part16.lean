import Boxes3971Part16
import Catalog3971
namespace PetersenNegated3971
theorem boxRange16 (r : Fin 32) : let idx := 512+r.val
  checkBox (bk idx,bm idx,br idx)=true := by
  fin_cases r
  · exact box_ok512
  · exact box_ok513
  · exact box_ok514
  · exact box_ok515
  · exact box_ok516
  · exact box_ok517
  · exact box_ok518
  · exact box_ok519
  · exact box_ok520
  · exact box_ok521
  · exact box_ok522
  · exact box_ok523
  · exact box_ok524
  · exact box_ok525
  · exact box_ok526
  · exact box_ok527
  · exact box_ok528
  · exact box_ok529
  · exact box_ok530
  · exact box_ok531
  · exact box_ok532
  · exact box_ok533
  · exact box_ok534
  · exact box_ok535
  · exact box_ok536
  · exact box_ok537
  · exact box_ok538
  · exact box_ok539
  · exact box_ok540
  · exact box_ok541
  · exact box_ok542
  · exact box_ok543
end PetersenNegated3971
