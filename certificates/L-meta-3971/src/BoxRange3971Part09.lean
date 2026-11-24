import Boxes3971Part09
import Catalog3971
namespace PetersenNegated3971
theorem boxRange9 (r : Fin 32) : let idx := 288+r.val
  checkBox (bk idx,bm idx,br idx)=true := by
  fin_cases r
  · exact box_ok288
  · exact box_ok289
  · exact box_ok290
  · exact box_ok291
  · exact box_ok292
  · exact box_ok293
  · exact box_ok294
  · exact box_ok295
  · exact box_ok296
  · exact box_ok297
  · exact box_ok298
  · exact box_ok299
  · exact box_ok300
  · exact box_ok301
  · exact box_ok302
  · exact box_ok303
  · exact box_ok304
  · exact box_ok305
  · exact box_ok306
  · exact box_ok307
  · exact box_ok308
  · exact box_ok309
  · exact box_ok310
  · exact box_ok311
  · exact box_ok312
  · exact box_ok313
  · exact box_ok314
  · exact box_ok315
  · exact box_ok316
  · exact box_ok317
  · exact box_ok318
  · exact box_ok319
end PetersenNegated3971
