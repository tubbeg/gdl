(ns gdl.scene2d.ui.table)

(defprotocol Table
  (cells [_])
  (add-rows [_ rows] "rows is a seq of seqs of columns.
                     Elements are actors or a map of
                     {:actor :expand? :bottom?  :colspan int :pad :pad-bottom}. Only :actor is required.")

  (add! [_ actor] "Adds a new cell to the table with the specified actor.")
  (add-separator! [_]))
