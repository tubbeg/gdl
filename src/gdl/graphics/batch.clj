(ns gdl.graphics.batch
  (:require [x.x :refer [defcomponent]]
            [gdl.lc :as lc])
  (:import com.badlogic.gdx.graphics.g2d.SpriteBatch))

(declare ^SpriteBatch batch) ; => in graphics ? *batch* ??
; binds a batch and start/end

(defcomponent (keyword (ns-name *ns*)) _
  (lc/create [_]
    (.bindRoot #'batch (SpriteBatch.)))
  (lc/dispose [_]
    (.dispose batch)))

; *batch*
; *shape-drawer*
; but its not thread local
; its 1 object for the whole lifecycle.
