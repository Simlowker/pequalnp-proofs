import Boxes3971Part12
import Catalog3971
namespace PetersenNegated3971
theorem boxRange12 (r : Fin 32) : let idx := 384+r.val
  checkBox (bk idx,bm idx,br idx)=true := by
  fin_cases r
  · exact box_ok384
  · exact box_ok385
  · exact box_ok386
  · exact box_ok387
  · exact box_ok388
  · exact box_ok389
  · exact box_ok390
  · exact box_ok391
  · exact box_ok392
  · exact box_ok393
  · exact box_ok394
  · exact box_ok395
  · exact box_ok396
  · exact box_ok397
  · exact box_ok398
  · exact box_ok399
  · exact box_ok400
  · exact box_ok401
  · exact box_ok402
  · exact box_ok403
  · exact box_ok404
  · exact box_ok405
  · exact box_ok406
  · exact box_ok407
  · exact box_ok408
  · exact box_ok409
  · exact box_ok410
  · exact box_ok411
  · exact box_ok412
  · exact box_ok413
  · exact box_ok414
  · exact box_ok415
end PetersenNegated3971
