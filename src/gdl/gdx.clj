(ns gdl.gdx
  (:require [x.x :refer [defcomponent]]
            [gdl.lc :as lc])
  (:import (com.badlogic.gdx Gdx
                             Application
                             Files
                             Graphics
                             Input)))

(declare ^Application app
         ^Files       files
         ^Graphics    graphics
         ^Input       input)

(defcomponent *ns* _
  (lc/create [_]
    (.bindRoot #'app      Gdx/app)
    (.bindRoot #'files    Gdx/files)
    (.bindRoot #'graphics Gdx/graphics)
    (.bindRoot #'input    Gdx/input) ))
