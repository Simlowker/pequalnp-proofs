import Boxes3971Part14
import Catalog3971
namespace PetersenNegated3971
theorem boxRange14 (r : Fin 32) : let idx := 448+r.val
  checkBox (bk idx,bm idx,br idx)=true := by
  fin_cases r
  · exact box_ok448
  · exact box_ok449
  · exact box_ok450
  · exact box_ok451
  · exact box_ok452
  · exact box_ok453
  · exact box_ok454
  · exact box_ok455
  · exact box_ok456
  · exact box_ok457
  · exact box_ok458
  · exact box_ok459
  · exact box_ok460
  · exact box_ok461
  · exact box_ok462
  · exact box_ok463
  · exact box_ok464
  · exact box_ok465
  · exact box_ok466
  · exact box_ok467
  · exact box_ok468
  · exact box_ok469
  · exact box_ok470
  · exact box_ok471
  · exact box_ok472
  · exact box_ok473
  · exact box_ok474
  · exact box_ok475
  · exact box_ok476
  · exact box_ok477
  · exact box_ok478
  · exact box_ok479
end PetersenNegated3971
