import Boxes3971Part10
import Catalog3971
namespace PetersenNegated3971
theorem boxRange10 (r : Fin 32) : let idx := 320+r.val
  checkBox (bk idx,bm idx,br idx)=true := by
  fin_cases r
  · exact box_ok320
  · exact box_ok321
  · exact box_ok322
  · exact box_ok323
  · exact box_ok324
  · exact box_ok325
  · exact box_ok326
  · exact box_ok327
  · exact box_ok328
  · exact box_ok329
  · exact box_ok330
  · exact box_ok331
  · exact box_ok332
  · exact box_ok333
  · exact box_ok334
  · exact box_ok335
  · exact box_ok336
  · exact box_ok337
  · exact box_ok338
  · exact box_ok339
  · exact box_ok340
  · exact box_ok341
  · exact box_ok342
  · exact box_ok343
  · exact box_ok344
  · exact box_ok345
  · exact box_ok346
  · exact box_ok347
  · exact box_ok348
  · exact box_ok349
  · exact box_ok350
  · exact box_ok351
end PetersenNegated3971
