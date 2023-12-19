(ns gdl.default-context
  (:require gdl.context.assets
            gdl.context.image-drawer-creator
            gdl.context.shape-drawer
            gdl.context.text-drawer
            gdl.context.sprite-batch
            gdl.context.ttf-generator
            gdl.context.gui-world-views
            gdl.context.vis-ui))

; TODO all context stuff ns-d keys !! at least without gui-stuff views for now...
; or just call 'create' ?
; and some are empty and just extending passing record class?

; separate gui & world-view => don't need in test
; only require what needed in test !!!
; remove default context !!

(defn ->Context [& {:keys [tile-size]}]
  (gdl.context/map->Context
   (let [context (gdl.context.sprite-batch/->context-map)]
     (merge context
            (gdl.context.vis-ui/load-and-create-context)
            (gdl.context.assets/->context-map)
            (gdl.context.text-drawer/->context-map)
            (gdl.context.shape-drawer/->context-map context)
            (gdl.context.gui-world-views/->context-map :tile-size (or tile-size 1))))))
