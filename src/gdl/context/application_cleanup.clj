(ns gdl.context.application-cleanup
  (:require gdl.context
            gdl.disposable)
  (:import com.badlogic.gdx.utils.Disposable))

(extend-type com.badlogic.gdx.utils.Disposable
  gdl.disposable/Disposable
  (dispose [this]
    (.dispose this)))

(extend-type gdl.context.Context
  gdl.context/ApplicationCleanup
  (dispose-all [context]
    (doseq [[k value] context
            :when (some #(extends? gdl.disposable/Disposable %)
                        (supers (class value)))]
      (println "Disposing " k)
      (gdl.disposable/dispose value))))

