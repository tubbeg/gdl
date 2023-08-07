(ns gdl.graphics.batch
  (:require [x.x :refer [defcomponent]]
            [gdl.lc :as lc])
  (:import com.badlogic.gdx.graphics.g2d.SpriteBatch))

(declare ^SpriteBatch batch)

(defcomponent *ns* _
  (lc/create [_]
    (.bindRoot #'batch (SpriteBatch.)))
  (lc/dispose [_]
    (.dispose batch)))
