from Fonctions.finales import *
import time
# on exécute le programme avec la liste de trajet avec une fenêtre de temps de plus de 5 min = 300s
start = time.time()
exec(tra_data,600,0)
end = time.time()
print("The time of execution of above program is :", end-start)