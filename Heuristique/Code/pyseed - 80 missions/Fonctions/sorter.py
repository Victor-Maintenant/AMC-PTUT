def takeTemps(elem):
    """
    Methode pour récuperer le temps de travail au sein de la methode 'sort()' de 'brancardiersPAR_ChargeDeTravail()'  
    """
    return int(elem["travail_cumule"])


def takeDepart(elem):
    """
    Methode pour récuperer l'heure de départ d'un trajet au sein de la methode 'sort()' de 'brancardiersPAR_ChargeDeTravail()'   
    """
    return elem["heure_depart"]


def takePriorite(elem):
    """
    Methode pour récuperer l'indice de priorite  au sein de la methode 'sort()' de 'tri'  
    """
    return elem["priorite"]

def takeOrdre(elem):
    return elem["ordre"]