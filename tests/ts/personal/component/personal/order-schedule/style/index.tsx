import { StyleSheet } from 'react-native';
import { Theme, CommonUtils, FONT_MUTIPLE } from '@hw-vmall/vrn-basic-comp';
export const WebScheduleStyle = (theme?: Theme) =>
  StyleSheet.create({
    scheduleContent: {
      width: '100%',
      paddingBottom: 12,
      paddingLeft: 12,
      paddingRight: 12,
      borderRadius: 8,
    },
    scheduleViewContent: {
      width: '100%',
      paddingBottom: 3,
      paddingLeft: 12,
      paddingRight: 12,
      borderRadius: 8,
      overflow: 'hidden',
    },
    scheduleViewBody: {
      paddingBottom: 9,
      overflow: 'hidden',
    },
    scheduleSwiper: {
      height: 56,
      width: '100%',
      borderRadius: 8,
      backgroundColor: theme.C32.color,
      opacity: theme.C83.opacity,
    },
    scheduleSwiperBody: {
      borderRadius: 8,
      backgroundColor: theme.C32.color,
      opacity: theme.C83.opacity,
    },
    scheduleBody: {
      width: '100%',
      borderRadius: 8,
      backgroundColor: theme.C32.color,
      opacity: theme.C83.opacity,
    },
    scheduleStatus: {
      marginLeft: 8,
      marginRight: 12,
      marginTop: 12,
      marginBottom: 12,
      justifyContent: 'center',
      flex: 1,
    },
    scheduleDesc: {
      flex: 1,
    },
    dotBox: {
      bottom: 7,
      margin: 0,
    },
    dot: {
      backgroundColor: CommonUtils.colorRgba(theme.C76.color, 0.1),
      minWidth: 4,
      width: 4,
      height: 4,
      borderRadius: 4,
      marginLeft: 4,
      marginRight: 4,
    },
    activeDot: {
      backgroundColor: theme.C42.color,
      width: 8,
      height: 4,
      borderRadius: 4,
      marginLeft: 4,
      marginRight: 4,
    },
    prdImg: {
      width: 48,
      height: 48,
      marginTop: 'auto',
      marginBottom: 'auto',
    },
    scheduleArea: {
      flexDirection: 'row',
    },
    scheduleItem: {
      marginTop: 'auto',
      marginBottom: 'auto',
    },
    scheduleDate: {
      alignItems: 'center',
      flexDirection: 'row',
      marginBottom: 2,
    },
    displayStatusDesc: {
      color: theme.C11.color,
      fontSize: CommonUtils.getScaleSize(theme.T4.fontSize, FONT_MUTIPLE.FONT_LEVEL_FIVE),
      fontWeight: '500',
    },
    displayStatusDescWap: {
      color: theme.C11.color,
      fontSize: CommonUtils.getScaleSize(theme.T4.fontSize, FONT_MUTIPLE.FONT_LEVEL_FIVE),
      fontWeight: '500',
      lineHeight: CommonUtils.getScaleSize(theme.T4.lineHeight, FONT_MUTIPLE.FONT_LEVEL_FIVE),
    },
    updateDate: {
      color: theme.C11.color,
      fontSize: CommonUtils.getScaleSize(theme.T2.fontSize, FONT_MUTIPLE.FONT_LEVEL_FIVE),
      fontWeight: '400',
      opacity: theme.C13.opacity,
      marginLeft: 8,
      lineHeight: CommonUtils.getScaleSize(theme.T4.lineHeight, FONT_MUTIPLE.FONT_LEVEL_FIVE),
    },
    progressDesc: {
      color: theme.C11.color,
      fontSize: CommonUtils.getScaleSize(theme.T2.fontSize, FONT_MUTIPLE.FONT_LEVEL_FIVE),
      fontWeight: '400',
      opacity: theme.C13.opacity,
      lineHeight: CommonUtils.getScaleSize(theme.T2.lineHeight, FONT_MUTIPLE.FONT_LEVEL_FIVE),
    }
  });
