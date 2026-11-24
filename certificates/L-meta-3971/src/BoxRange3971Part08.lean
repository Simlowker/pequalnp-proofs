import Boxes3971Part08
import Catalog3971
namespace PetersenNegated3971
theorem boxRange8 (r : Fin 32) : let idx := 256+r.val
  checkBox (bk idx,bm idx,br idx)=true := by
  fin_cases r
  · exact box_ok256
  · exact box_ok257
  · exact box_ok258
  · exact box_ok259
  · exact box_ok260
  · exact box_ok261
  · exact box_ok262
  · exact box_ok263
  · exact box_ok264
  · exact box_ok265
  · exact box_ok266
  · exact box_ok267
  · exact box_ok268
  · exact box_ok269
  · exact box_ok270
  · exact box_ok271
  · exact box_ok272
  · exact box_ok273
  · exact box_ok274
  · exact box_ok275
  · exact box_ok276
  · exact box_ok277
  · exact box_ok278
  · exact box_ok279
  · exact box_ok280
  · exact box_ok281
  · exact box_ok282
  · exact box_ok283
  · exact box_ok284
  · exact box_ok285
  · exact box_ok286
  · exact box_ok287
end PetersenNegated3971
