"""
for logging
"""
import logging

def reg_logger():
    """
    regist a logger
    """
    FORMAT = '%(asctime)-15s %(levelname)s: %(message)s'
    DATEFORMATE = '%m/%d %I:%M:%S'

    logging.basicConfig(format=FORMAT, datefmt=DATEFORMATE,
                        level=logging.DEBUG,
                        filename='log/autoprover.log')
